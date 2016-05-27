Add LoadPath "..".

Require Import ILSyntax.
Require Import Syntax.
Require Import Reals.
Require Import Utils.
Require Import List.
Require Import Environments.
Require Import Denotational.
Require Import Arith.
Require Import Recdef.
Require Import Coq.Program.Wf.

Import ListNotations.

Inductive ILVal : Set :=
| ILBVal : bool -> ILVal
| ILRVal : R -> ILVal
| ILNVal : nat -> ILVal.


Definition fromRVal (v : ILVal) :=
  match v with
    | ILRVal v' => Some v'
    | _ => None
  end.

Definition fromBVal (v : ILVal) :=
  match v with
    | ILBVal v' => Some v'
    | _ => None
  end.

Fixpoint toListR (vs : list ILVal) : option (list R):=
  match vs with
    | v :: vs' => match v with
                    | ILRVal r => Some r >>= fun x => toListR vs' >>= fun y => pure (x :: y)
                    | _ => None
                  end                    
    | [] => Some []
  end.

(*Definition translateILVal v :=
  match v with
    | ILRVal r => RVal r
    | ILBVal b => BVal b
  end.*)

Definition fromVal v :=
  match v with
    | RVal r => ILRVal r
    | BVal b => ILBVal b
  end.

Definition fromExtEnv (extC: ExtEnv' Val) :=
  fun l t => fromVal (extC l t).

Fixpoint ILBinOpSem (op : ILBinOp) (v1 v2 : ILVal) : option ILVal :=
  match op, v1, v2 with
    | ILAdd, ILRVal v1', ILRVal v2' => Some (ILRVal (v1' + v2'))
    | ILSub, ILRVal v1', ILRVal v2' => Some (ILRVal (v1' - v2'))
    | ILMult, ILRVal v1', ILRVal v2' => Some (ILRVal (v1' * v2'))
    | ILDiv, ILRVal v1', ILRVal v2' => Some (ILRVal (v1' / v2'))
    | ILAnd, ILBVal v1', ILBVal v2' => Some (ILBVal (v1' && v2'))
    | ILOr, ILBVal v1', ILBVal v2' => Some (ILBVal (v1' || v2'))
    | ILLess, ILRVal v1', ILRVal v2' => Some (ILBVal (Rltb v1' v2'))
    | ILLeq, ILRVal v1', ILRVal v2' => Some (ILBVal (Rleb v1'  v2'))
    | ILEqual, ILRVal v1', ILRVal v2' => Some (ILBVal (Reqb v1' v2'))
    | ILLessN, ILNVal n1, ILNVal n2 => Some (ILBVal (NPeano.ltb n1 n2))
    | _, _, _ => None
  end.

Fixpoint ILUnOpSem (op : ILUnOp) (v : ILVal) : option ILVal :=
  match op with
    | ILNot => fromBVal v >>= fun v' => pure (ILBVal (negb v'))
    | ILNeg => fromRVal v >>= fun v' => pure (ILRVal (-v'))
  end.

Reserved Notation "'IL[|' e '|]'" (at level 9).
Reserved Notation "'ILk[|' e '|]'" (at level 9).

Definition eval_payoff disc_val p1 p2 p1' p2' :=
  if ((Party.eqb p1 p1') && (Party.eqb p2 p2')) then (ILRVal disc_val)
  else if ((Party.eqb p2 p1') && (Party.eqb p1 p2')) then (ILRVal (-disc_val))
       else (ILRVal 0).

Local Open Scope Z.

Definition Zsum_list xs := fold_right Zplus 0%Z xs.

Fixpoint ILTexprSem t tenv :=
  match t with
    | ILTplus t1 t2 => (ILTexprSem t1 tenv + ILTexprSem t2 tenv)%nat
    | ILTexpr t1 => TexprSem t1 tenv
  end.

Fixpoint ILTexprSemZ t tenv :=
  match t with
    | ILTplusZ z t2 => (z + Z.of_nat (ILTexprSem t2 tenv))
    | ILTexprZ t1 => Z.of_nat (ILTexprSem t1 tenv)
  end.


Local Close Scope Z.

Fixpoint loop_if_sem n t0 b e1 e2 : option ILVal:=
  b t0 >>=
       fun b' => match b' with
                   | ILBVal true => e1 t0
                   | ILBVal false =>
                     match n with
                       | O => e2 t0
                       | S n' => loop_if_sem n' (S t0) b e1 e2
                     end                                               
                   | _ => None
                 end.

Fixpoint ILsem (e : ILExpr) (ext : ExtEnv' ILVal) (tenv : TEnv) (t0 : nat) disc p1 p2 : option ILVal:=
  match e with
    | ILUnExpr op e1 => IL[|e1|] ext tenv t0 disc p1 p2 >>= fun v => ILUnOpSem op v
    | ILBinExpr op e1 e2 => IL[|e1|] ext tenv t0 disc p1 p2 >>=
                            fun v1 => IL[|e2|] ext tenv t0 disc p1 p2 >>=
                                        fun v2 => ILBinOpSem op v1 v2
    | ILIf b e1 e2 => IL[|b|] ext tenv t0 disc p1 p2 >>=
                        fun b' => match b' with
                                    | ILBVal true => IL[|e1|] ext tenv t0 disc p1 p2
                                    | ILBVal false => IL[|e2|] ext tenv t0 disc p1 p2
                                    | _ => None
                                  end
    | ILLoopIf b e1 e2 t => let n:= (TexprSem t tenv) in
                            loop_if_sem n t0
                                         (fun t => IL[|b|] ext tenv t disc p1 p2)
                                         (fun t => IL[|e1|] ext tenv t disc p1 p2)
                                         (fun t => IL[|e2|] ext tenv t disc p1 p2)
    | FloatV v => Some (ILRVal v)
    | NatV v => Some (ILNVal v)
    | Model lab t => Some (ext lab (Z.of_nat t0 + (ILTexprSemZ t tenv))%Z)
    | ILtexpr e_t => Some (ILNVal (ILTexprSem e_t tenv))
    | Payoff t p1' p2' => Some (eval_payoff (disc (t0 + (ILTexprSem t tenv))) p1' p2' p1 p2)
  end
  where "'IL[|' e '|]'" := (ILsem e).

Axiom X : Party.
Axiom Y : Party.
Axiom Lab : RealObs.

Eval compute in
    (ILsem (ILBinExpr ILAdd (Model (LabR Lab) (ILTexprZ (ILTexpr (Tnum 0)))) (FloatV 20))
           (fun _ t => if (beq_nat (Z.to_nat t) 0) then (ILRVal 100) else (ILRVal 0))
           (fun _ => 0) 0 (fun _ => 1%R) X Y).


(*
Fixpoint ILsem_k (e : ILExpr) (env : Env' ILVal) (ext : ExtEnv' ILVal) (envT : TEnv) disc p1 p2 (k : nat) : option ILVal:=
  match e with
    | ILUnExpr op e1 => ILk[|e1|] env ext envT disc p1 p2 k >>= fun v => ILUnOpSem op v
    | ILBinExpr op e1 e2 => ILk[|e1|] env ext envT disc p1 p2 k >>=
                            fun v1 => ILk[|e2|] env ext envT disc p1 p2 k >>=
                                        fun v2 => ILBinOpSem op v1 v2
    | ILIf b e1 e2 => ILk[|b|] env ext envT disc p1 p2 k >>=
                        fun b' => ILk[|e1|] env ext envT disc p1 p2 k >>=
                                    fun e1' => ILk[|e2|] env ext envT disc p1 p2 k >>=
                                                 fun e2' => match b', e1', e2' with
                                                              | ILBVal true, ILRVal v1, _ => pure (ILRVal v1)
                                                              | ILBVal false, _, ILRVal v2 => pure (ILRVal v2)
                                                              | _ , _, _ => None
                                                            end
    | FloatV v => Some (ILRVal v)
    | Model lab t => Some (ext lab (evalTexpr t envT))
    | Payoff e_t p1' p2' => let t := Z.to_nat (evalTexpr e_t envT) in
                            if (NPeano.ltb t k) then (Some (ILRVal 0))
                            else Some (eval_payoff (disc t) p1' p2' p1 p2)    
  end
where "'ILk[|' e '|]'" := (ILsem_k e).
*)
