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

Local Open Scope Z.

Definition Zsum_list xs := fold_right Zplus 0%Z xs.

Definition ILTexprSem t tenv :=
  match t with
    | ILTnumZ z => z
    | ILTexpr e => Z.of_nat (TexprSem e tenv)
  end.

Fixpoint evalILTexpr0 t0 ts tenv :=
  match ts with
    | hd :: tl => ILTexprSem hd tenv + evalILTexpr0 t0 tl tenv
    | [] => t0
  end.

Definition evalILTexpr := evalILTexpr0 0%Z.

Local Close Scope Z.
(*
Fixpoint pushForward' (t : nat) (e : ILExpr) : ILExpr :=
  match e with
    | ILIf b e1 e2 => ILIf (pushForward' t b) (pushForward' t e1) (pushForward' t e2)
    | Model s t' => Model s (Tnum t :: t')
    | ILUnExpr op e1 => ILUnExpr op (pushForward' t e1)
    | ILBinExpr op e1 e2 => ILBinExpr op (pushForward' t e1) (pushForward' t e2)
    | FloatV v => FloatV v
    | Payoff t' p1 p2 => Payoff (Tnum t :: t') p1 p2
    | ILLoopIf b e1 e2 ts => ILLoopIf (pushForward' t b) (pushForward' t e1) (pushForward' t e2) (Tnum t :: ts)
  end.
*)
(*Fixpoint loop_if_sem (b e1 e2 : ILExpr) (n : nat) sem :=
  sem b >>=
    fun b' =>
      match b' with
        | ILBVal true => sem e1
        | ILBVal false =>
          match n with
            | 0 => sem e2
            | S n' => loop_if_sem (pushForward' 1 b) (pushForward' 1 e1) (pushForward' 1 e2) n' sem
          end
        | _ => None
      end.*)

Fixpoint ilexpr_size e :=
  match e with
    | ILIf e0 e1 e2 => ilexpr_size e0 + ilexpr_size e1 + ilexpr_size e2 + 1
    | FloatV _ => 1
    | Model _ _ => 1
    | ILUnExpr _ e => 1 + ilexpr_size e
    | ILBinExpr _ e1 e2 => ilexpr_size e1 + ilexpr_size e2 + 1
    | ILLoopIf e0 e1 e2 _ => ilexpr_size e0 + ilexpr_size e1 + ilexpr_size e2 + 1
    | Payoff _ _ _ => 1
  end.
(*
Lemma pushForward_same_size e n: ilexpr_size e = ilexpr_size (pushForward' n e).
Proof.
  induction e; simpl; omega.
Qed.
*)
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

Check ILLoopIf.

Fixpoint ILsem (e : ILExpr) (env : Env' ILVal) (ext : ExtEnv' ILVal) (tenv : TEnv) (t0 : nat) disc p1 p2 : option ILVal:=
  match e with
    | ILUnExpr op e1 => IL[|e1|] env ext tenv t0 disc p1 p2 >>= fun v => ILUnOpSem op v
    | ILBinExpr op e1 e2 => IL[|e1|] env ext tenv t0 disc p1 p2 >>=
                            fun v1 => IL[|e2|] env ext tenv t0 disc p1 p2 >>=
                                        fun v2 => ILBinOpSem op v1 v2
    | ILIf b e1 e2 => IL[|b|] env ext tenv t0 disc p1 p2 >>=
                        fun b' => IL[|e1|] env ext tenv t0 disc p1 p2 >>=
                                    fun e1' => IL[|e2|] env ext tenv t0 disc p1 p2 >>=
                                                 fun e2' => match b', e1', e2' with
                                                              | ILBVal true, ILRVal v1, _ => pure (ILRVal v1)
                                                              | ILBVal false, _, ILRVal v2 => pure (ILRVal v2)
                                                              | _ , _, _ => None
                                                            end
    | ILLoopIf b e1 e2 t => let n:= (TexprSem t tenv) in
                            loop_if_sem n t0
                                         (fun t => IL[|b|] env ext tenv t disc p1 p2)
                                         (fun t => IL[|e1|] env ext tenv t disc p1 p2)
                                         (fun t => IL[|e2|] env ext tenv t disc p1 p2)
    (*let nn := (Z.to_nat (evalTexpr t tenv)) in
                            (fix loop_if_sem n :=
                               let n0 := nn - n
                               in IL[|b|] env ext tenv (t0 + n0) disc p1 p2 >>=
                                    fun b' => match b' with
                                                | ILBVal true => IL[|e1|] env ext tenv (t0 + n0) disc p1 p2
                                                | ILBVal false =>
                                                  match n with
                                                    | O => IL[|e2|] env ext tenv (t0 + n0) disc p1 p2
                                                    | S n' => loop_if_sem n'
                                                  end                                               
                                                | _ => None
                                              end) nn*)
    | FloatV v => Some (ILRVal v)
    | Model lab t => Some (ext lab (Z.of_nat t0 + (evalILTexpr t tenv))%Z)
    | Payoff t p1' p2' => Some (eval_payoff (disc (Z.of_nat t0 + (evalILTexpr t tenv))%Z) p1' p2' p1 p2)
  end
  where "'IL[|' e '|]'" := (ILsem e).
(*
Program Fixpoint ILsem (e : ILExpr) (env : Env' ILVal) (ext : ExtEnv' ILVal)
        (envT : TEnv) disc p1 p2 {measure (ilexpr_size e)}: option ILVal:=
  match e with
    | ILUnExpr op e1 => let v' := (ILsem e1 env ext envT disc p1 p2) in
                        match v' with
                          | Some v  => ILUnOpSem op v
                          | None => None
                        end
    | ILBinExpr op e1 e2 => ILsem e1 env ext envT disc p1 p2 >>=
                            fun v1 => ILsem e2 env ext envT disc p1 p2 >>=
                                        fun v2 => ILBinOpSem op v1 v2
    (*let v1' := (ILsem e1 env ext envT disc p1 p2) in
                            match v1' with
                              | Some v1  => let v2' := (ILsem e2 env ext envT disc p1 p2) in
                                            match v2'  with
                                              | Some v2 => ILBinOpSem op v1 v2
                                              | None => None
                                            end
                              | None => None
                            end*)
    | ILIf b e1 e2 => match (ILsem b env ext envT disc p1 p2) with
                        | Some (ILBVal true) => ILsem e1 env ext envT disc p1 p2
                        | Some (ILBVal false) => ILsem e2 env ext envT disc p1 p2
                        | Some (ILRVal r) => None
                        | None => None
                      end
    (*| ILIf b e1 e2 => ILsem b env ext envT disc p1 p2 >>=
                        fun b' => ILsem e1 env ext envT disc p1 p2 >>=
                                    fun e1' => ILsem e2 env ext envT disc p1 p2 >>=
                                                 fun e2' => match b', e1', e2' with
                                                              | ILBVal true, ILRVal v1, _ => pure (ILRVal v1)
                                                              | ILBVal false, _, ILRVal v2 => pure (ILRVal v2)
                                                              | _ , _, _ => None
                                                            end*)
    | ILLoopIf b'' e1' e2' t =>
      (fix loop_if_sem n :=
         let n0 := n - (Z.to_nat (evalTexpr t envT))
         in match (ILsem (pushForward' n0 b'') env ext envT disc p1 p2) with
               | Some (ILBVal true) =>  ILsem e1' env ext envT disc p1 p2
               | Some (ILBVal false) =>
                 match n with
                   | 0 =>  ILsem (pushForward' n0 e2') env ext envT disc p1 p2
                   | S n' => loop_if_sem n'
                 end
               | v => None
             end) (Z.to_nat (evalTexpr t envT))

     (*(fix loop_if_sem n (b: ILExpr) :=
                               IL[|b|] env ext envT disc p1 p2>>=
                                 fun b' =>
                                   match b' with
                                     | ILBVal true =>  IL[|e1'|] env ext envT disc p1 p2
                                     | ILBVal false =>
                                       match n with
                                         | 0 =>  IL[|e2'|] env ext envT disc p1 p2
                                         | S n' => loop_if_sem n' (pushForward' 1 b)
                                       end
                                     | _ => None
                                   end) (Z.to_nat (evalTexpr t envT)) b'' *)
      (*loop_if_sem b e1 e2
                                        (Z.to_nat (evalTexpr t envT)) envT
                                        (fun e => ILsem e env ext envT disc p1 p2)*)
    | FloatV v => Some (ILRVal v)
    | Model lab t => Some (ext lab (evalTexpr t envT))
    | Payoff t p1' p2' => Some (eval_payoff (disc (evalTexpr t envT)) p1' p2' p1 p2)
  end.
(*Obligation Tactic := (intros; subst; simpl; try omega).*)
Next Obligation. (intros; subst; simpl; try omega).
Qed.
Next Obligation. (intros; subst; simpl; try omega).
Qed.
Next Obligation. (intros; subst; simpl; try omega).
Qed.
Next Obligation. (intros; subst; simpl; try omega).
Qed.
Next Obligation. (intros; subst; simpl; try omega).
Qed.
Next Obligation. (intros; subst; simpl; try omega). simpl in *. rewrite <- pushForward_same_size. omega.
Defined.
Next Obligation. (intros; subst; simpl; try omega).
Defined.
Next Obligation. (intros; subst; simpl; try omega). simpl in *. rewrite <- pushForward_same_size. omega.
Defined.
Next Obligation. apply conj. unfold not. intros. inversion H. unfold not. intros. inversion H.
Defined.
Next Obligation. (intros; subst; simpl; try omega). apply conj. unfold not. intros. inversion H. unfold not. intros. inversion H.
Defined.
*)
Check ILsem.

Axiom X : Party.
Axiom Y : Party.
Axiom Lab : RealObs.

Eval compute in
    (ILsem (ILBinExpr ILAdd (Model (LabR Lab) [ILTexpr (Tnum 0)]) (FloatV 20))
           [] (fun _ t => if (beq_nat (Z.to_nat t) 0) then (ILRVal 100) else (ILRVal 0))
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
