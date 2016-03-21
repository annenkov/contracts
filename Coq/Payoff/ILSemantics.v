Add LoadPath "..".

Require Import ILSyntax.
Require Import Reals.
Require Import Utils.
Require Import List.
Require Import Environments.
Require Import Denotational.
Require Import Arith.

Import ListNotations.

Inductive ILVal : Set :=
| ILBVal : bool -> ILVal
| ILRVal : R -> ILVal.


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

Definition translateILVal v :=
  match v with
    | ILRVal r => RVal r
    | ILBVal b => BVal b
  end.

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
   

Fixpoint ILsem (e : ILExpr) (env : Env' ILVal) (ext : ExtEnv' ILVal) disc p1 p2 : option ILVal:=
  match e with
    | ILUnExpr op e1 => IL[|e1|] env ext disc p1 p2 >>= fun v => ILUnOpSem op v
    | ILBinExpr op e1 e2 => IL[|e1|] env ext disc p1 p2 >>=
                            fun v1 => IL[|e2|] env ext disc p1 p2 >>=
                                        fun v2 => ILBinOpSem op v1 v2
    | ILIf b e1 e2 => IL[|b|] env ext disc p1 p2 >>=
                        fun b' => IL[|e1|] env ext disc p1 p2 >>=
                                    fun e1' => IL[|e2|] env ext disc p1 p2 >>=
                                                 fun e2' => match b', e1', e2' with
                                                              | ILBVal true, ILRVal v1, _ => pure (ILRVal v1)
                                                              | ILBVal false, _, ILRVal v2 => pure (ILRVal v2)
                                                              | _ , _, _ => None
                                                            end
    | FloatV v => Some (ILRVal v)
    | Model lab t => Some (ext lab t)
    | Payoff t p1' p2' => Some (eval_payoff (disc t) p1' p2' p1 p2)
  end
  where "'IL[|' e '|]'" := (ILsem e).

SearchPattern (nat -> bool).

Fixpoint ILsem_k (e : ILExpr) (env : Env' ILVal) (ext : ExtEnv' ILVal) disc p1 p2 (k : nat) : option ILVal:=
  match e with
    | ILUnExpr op e1 => ILk[|e1|] env ext disc p1 p2 k >>= fun v => ILUnOpSem op v
    | ILBinExpr op e1 e2 => ILk[|e1|] env ext disc p1 p2 k >>=
                            fun v1 => ILk[|e2|] env ext disc p1 p2 k >>=
                                        fun v2 => ILBinOpSem op v1 v2
    | ILIf b e1 e2 => ILk[|b|] env ext disc p1 p2 k >>=
                        fun b' => ILk[|e1|] env ext disc p1 p2 k >>=
                                    fun e1' => ILk[|e2|] env ext disc p1 p2 k >>=
                                                   fun e2' => match b', e1', e2' with
                                                                | ILBVal true, ILRVal v1, _ => pure (ILRVal v1)
                                                                | ILBVal false, _, ILRVal v2 => pure (ILRVal v2)
                                                                | _ , _, _ => None
                                                              end
    | FloatV v => Some (ILRVal v)
    | Model lab t => Some (ext lab t)
    | Payoff t p1' p2' => if (NPeano.ltb t k) then (Some (ILRVal 0))
                          else Some (eval_payoff (disc t) p1' p2' p1 p2)
  end
where "'ILk[|' e '|]'" := (ILsem_k e).
