Add LoadPath "..".

Require Import ZArith.
Require Import List.
Require Import String.
Require Import Syntax.
Require Import Denotational.
Require Import Specialise.
Require Import Tactics.
Require Import Utils.
Require Import Setoid.
Require Import Misc.
Require Import FunctionalExtensionality.

Import ListNotations.
Open Scope string_scope.

Inductive ILBinOp : Set := ILAdd | ILSub | ILMult | ILDiv | ILAnd | ILOr |
                           ILLess | ILLeq | ILEqual.

Inductive ILUnOp : Set := ILNot | ILNeg.


Inductive ILExpr : Set :=
| ILIf : ILExpr -> ILExpr -> ILExpr -> ILExpr
| FloatV : R -> ILExpr
| Model : ObsLabel -> Z -> ILExpr
| ABExpr1 : ILUnOp -> ILExpr -> ILExpr
| ABExpr2 : ILBinOp -> ILExpr -> ILExpr -> ILExpr
| Payoff  : Party -> Party -> ILExpr. 

Inductive ILVal : Set :=
| ILBVal : bool -> ILVal
| ILRVal : R -> ILVal
| ILAVal : list R -> ILVal.

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

Definition fromAVal (v : ILVal) :=
  match v with
    | ILAVal v' => Some v'
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

Definition eval_payoff p1 p2 p1' p2' :=
  if ((Party.eqb p1 p1') && (Party.eqb p2 p2')) then (ILRVal 1)
  else if ((Party.eqb p2 p1') && (Party.eqb p1 p2')) then (ILRVal (-1))
       else (ILRVal 0).
   

Fixpoint ILsem (e : ILExpr) (env : Env' ILVal) (ext : ExtEnv' ILVal) p1 p2 : option ILVal:=
  match e with
    | ABExpr1 op e1 => IL[|e1|] env ext p1 p2 >>= fun v => ILUnOpSem op v
    | ABExpr2 op e1 e2 => IL[|e1|] env ext p1 p2>>=
                            fun v1 => IL[|e2|] env ext p1 p2 >>=
                                        fun v2 => ILBinOpSem op v1 v2
    | ILIf b e1 e2 => match (IL[|b|] env ext p1 p2),(IL[|e1|] env ext p1 p2),(IL[|e2|] env ext p1 p2) with
                        | Some (ILBVal b'), Some (ILRVal e1'), Some (ILRVal e2') =>
                            Some (ILRVal (if b' then e1' else e2'))
                        | Some (ILBVal b'), Some (ILAVal e1'), Some (ILAVal e2') =>
                            Some (ILAVal (if b' then e1' else e2'))
                        | Some (ILBVal b'), Some (ILBVal e1'), Some (ILBVal e2') =>
                            Some (ILBVal (if b' then e1' else e2'))
                        | _, _, _ => None
                      end
    | FloatV v => Some (ILRVal v)
    | Model lab t => Some (ext lab t)
    | Payoff p1' p2' => Some (eval_payoff p1' p2' p1 p2)
  end
  where "'IL[|' e '|]'" := (ILsem e).
    
Eval compute in ILsem (ABExpr2 ILSub (ABExpr2 ILAdd (FloatV 1) (FloatV 2)) (FloatV 1)) [] (fun _ _ => ILRVal 0).
         
Fixpoint fromExp (env : Env' ILExpr) (t0 : Z) (e : Exp) :=
  match e with
    | OpE Add [a1;a2] => (fromExp env t0 a1) >>= (fun v1 =>
                           (fromExp env t0 a2) >>= (fun v2 =>
                             pure (ABExpr2 ILAdd v1 v2)))
    | OpE Sub [a1;a2] => (fromExp env t0 a1) >>= (fun v1 =>
                           (fromExp env t0 a2) >>= (fun v2 =>
                             pure (ABExpr2 ILSub v1 v2)))
    | OpE Mult [a1;a2] => (fromExp env t0 a1) >>= fun v1 =>
                             (fromExp env t0 a2) >>= fun v2 => pure (ABExpr2 ILMult v1 v2)
    | OpE Div [a1;a2] => (fromExp env t0 a1) >>= (fun v1 =>
                           (fromExp env t0 a2) >>= (fun v2 =>
                             pure (ABExpr2 ILDiv v1 v2)))
    | OpE And [a1;a2] => (fromExp env t0 a1) >>= (fun v1 =>
                           (fromExp env t0 a2) >>= (fun v2 =>
                             pure (ABExpr2 ILAnd v1 v2)))
    | OpE Or [a1;a2] => (fromExp env t0 a1) >>= (fun v1 =>
                           (fromExp env t0 a2) >>= (fun v2 =>
                             pure (ABExpr2 ILOr v1 v2)))
    | OpE Less [a1;a2] => (fromExp env t0 a1) >>= (fun v1 =>
                           (fromExp env t0 a2) >>= (fun v2 =>
                             pure (ABExpr2 ILLess v1 v2)))
    | OpE Leq [a1;a2] => (fromExp env t0 a1) >>= (fun v1 =>
                           (fromExp env t0 a2) >>= (fun v2 =>
                             pure (ABExpr2 ILLeq v1 v2)))
    | OpE Equal [a1;a2] => (fromExp env t0 a1) >>= (fun v1 =>
                           (fromExp env t0 a2) >>= (fun v2 =>
                             pure (ABExpr2 ILEqual v1 v2)))
    | OpE (RLit v) _ => Some (FloatV v)
    | OpE _ _ => None
    | Obs lab t => Some (Model lab (t0 + t))
    | VarE n => None
    | Acc _ _ _ => None
  end.

Definition R_ r := OpE (RLit r) [].

Example simple_expr_translation :
  fromExp [] 0 (OpE Sub [(OpE Add [R_ 1; R_ 2]); R_ 1]) = Some (ABExpr2 ILSub (ABExpr2 ILAdd (FloatV 1) (FloatV 2)) (FloatV 1)).
Proof.
  reflexivity.
Qed.

Eval compute in ((Esem (OpE Mult [(OpE Add [R_ 1; R_ 2]); R_ 1])) [] (fun (_: ObsLabel) (_ : Z) => RVal 0)).

Fixpoint pushForward (t : nat) (e : ILExpr) : ILExpr :=
  match e with
    | ILIf b e1 e2 => ILIf (pushForward t b) (pushForward t e1) (pushForward t e2)
    | Model s t' => Model s (Z.add (Z.of_nat t) t')
    | ABExpr1 op e1 => ABExpr1 op (pushForward t e1)
    | ABExpr2 op e1 e2 => ABExpr2 op (pushForward t e1) (pushForward t e2)
    | FloatV v => FloatV v
    | Payoff p1 p2 => Payoff p1 p2
  end.

Fixpoint nestedIfs (env : Env' ILExpr) (cond : Exp) (t' : nat) (t0 : Z)
                   (c1 : ILExpr) (c2 : ILExpr) : option ILExpr :=
  match t' with
    | 0 => match (fromExp env t0 cond) with
             | Some v => Some (ILIf v c1 c2)
             | None => None
           end
    | S t'' => match (fromExp env (Z.of_nat t') cond) with
                | Some v => (nestedIfs env cond t'' t0 c1 c2) >>= fun v' => Some (ILIf v (pushForward 1 c1) v')
                | None => None
              end
  end.

Fixpoint fromContr (env : Env' ILExpr) (c : Contr) (t0 : nat) : option ILExpr:=
  match c with
    | Scale e c      => fromExp env (Z.of_nat t0) e
                                >>= fun v => (fromContr env c t0)
                                               >>= fun v' => pure (ABExpr2 ILMult v v')                          
    | Translate t' c => fromContr env c (t' + t0)
    | If e t' c1 c2  => (fromContr env c1 t0)
                          >>= fun v1 => (fromContr env c2 (t0 + t'))
                                          >>= fun v2 => nestedIfs env e t' (Z.of_nat t0) v1 v2
    | Zero           => Some (FloatV 0)
    | Let e c        => (fromExp env (Z.of_nat t0) e)
                          >>= fun v => fromContr (v :: env) c t0                          
    | Transfer p1 p2 _ => Some (if (Party.eqb p1 p2) then (FloatV 0) else (Payoff p1 p2))
    | Both c1 c2     => (fromContr env c1 t0)
                          >>= fun v1 => (fromContr env c2 t0)
                                          >>= fun v2 => pure (ABExpr2 ILAdd v1 v2)
  end.

Definition translateILVal v :=
  match v with
    | ILRVal r => RVal r
    | ILBVal b => BVal b
    | ILAVal xs => RVal (fold_left Rplus xs 0%R) 
  end.

Lemma all_to_forall1 {A} P (x : A) :
  all P [x] -> P x.
Proof.
  intros. inversion H. subst. assumption.
Qed.
     
Lemma all_to_forall2 {A} P (x1 : A) (x2 : A) :
  all P [x1;x2] -> P x1 /\ P x2.
Proof.
  intros. inversion H. subst. split.
  - assumption.
  - apply all_to_forall1 in H3. assumption.
Qed.


Lemma translateILVal_RVal_f_eq f x1 x2 y1 y2:
  RVal x1 = translateILVal (ILRVal y1) ->
  RVal x2 = translateILVal (ILRVal y2) ->
  RVal (f x1 x2) = translateILVal (ILRVal (f y1 y2)).
Proof.
  intros. simpl in *. inversion H. inversion H0. subst. reflexivity.
Qed.

Lemma translateILVal_BVal_f_eq f x1 x2 y1 y2:
  BVal x1 = translateILVal (ILBVal y1) ->
  BVal x2 = translateILVal (ILBVal y2) ->
  BVal (f x1 x2) = translateILVal (ILBVal (f y1 y2)).
Proof.
  intros. simpl in *. inversion H. inversion H0. subst. reflexivity.
Qed.

Lemma translateILVal_BVal_f_eq' f x1 x2 y1 y2:
  RVal x1 = translateILVal (ILRVal y1) ->
  RVal x2 = translateILVal (ILRVal y2) ->
  BVal (f x1 x2) = translateILVal (ILBVal (f y1 y2)).
Proof.
  intros. simpl in *. inversion H. inversion H0. subst. reflexivity.
Qed.

(*Lemma ILExpr_OpSem_sound op args envIL extIL :
  OpSem op args = liftM translateILVal (IL[|fromExp [] 0 (OpE op args) |] envIL extIL).*)

Ltac destruct_vals := repeat (match goal with
                        | [x : Val |- _] => destruct x; tryfalse
                        | [x : ILVal |- _] => destruct x; tryfalse
                      end).
Ltac some_inv := repeat (unfold pure in *; match goal with
                   | [H: Some _ = Some _ |- _] => inversion H; clear H
                 end).

Theorem Exp_translation_sound : forall (e : Exp) (il_e : ILExpr) (envC : Env' Val) (extC : ExtEnv' Val)
                                          (envIL : Env' ILVal) (extIL : ExtEnv' ILVal) (envILtrans : Env' ILExpr)
                                          (v : Val) (v' : ILVal) p1 p2 t0,
  fromExp envILtrans t0 e = Some il_e ->
  (forall l t, extC l t = translateILVal (extIL l t)) ->
  E[|e|] envC (adv_ext t0 extC) = Some v ->
  IL[|il_e|] envIL extIL p1 p2 = Some v'->
  v = translateILVal v'.
Proof.
  intros. generalize dependent envC. generalize dependent extC.
  generalize dependent envIL. generalize dependent extIL. generalize dependent envILtrans.
  generalize dependent il_e. generalize dependent v. generalize dependent v'.
  (*generalize dependent t.  generalize dependent oLab.*)

  induction e using Exp_ind'.

  + (* OpE *)
    (* Binary*)
    intros; destruct op;
    simpl in *; do 3 try (destruct args; tryfalse); tryfalse; simpl in *;
                option_inv_auto; subst; simpl in *; try (some_inv); subst; simpl in *; subst;
                option_inv_auto; subst; simpl in *; destruct_vals;
                subst; option_inv_auto;
      try (apply all_to_forall2 in H; inversion_clear H as [IHe IHe0]);
      try (apply translateILVal_RVal_f_eq); try (apply translateILVal_BVal_f_eq); try (apply translateILVal_BVal_f_eq');
      try (eapply IHe; eassumption); try (eapply IHe0; eassumption).
    reflexivity.
  + (* Obs *)
    intros. simpl in *. some_inv. subst. simpl in *. some_inv. subst. eapply H0.
  + (* Var *)
    intros. inversion H.
  + (* Acc *)
    intros. inversion H.
Qed.

Lemma of_nat_plus x y:
  Z.add (Z.of_nat x) (Z.of_nat y) = Z.of_nat (x + y)%nat.
Proof.
  generalize dependent y.
  induction x as [| x'].
  - intros. reflexivity.
  - intros. rewrite Zplus_comm. rewrite <- succ_of_nat. rewrite plus_comm. rewrite <- plus_n_Sm. rewrite Zplus_0_r_reverse.
    replace (Z.of_nat (S (y + x')) + 0)%Z with (0 + (Z.of_nat (S (y + x'))))%Z. rewrite <- succ_of_nat with (t:=0%Z).
    rewrite <- Zplus_assoc. rewrite (Zplus_comm (Z.of_nat y) (1 + Z.of_nat x')).
    rewrite Zplus_0_l. rewrite <- Zplus_assoc. apply Zplus_eq_compat. reflexivity. rewrite plus_comm. apply IHx'. apply Zplus_comm.
Qed.

Lemma delay_scale_trace tr t n :
  scale_trace  n (delay_trace t tr) = delay_trace t (scale_trace n tr).
Proof.
  unfold scale_trace, delay_trace, compose. apply functional_extensionality. intros. destruct (leb t x).
  - reflexivity.
  - apply scale_empty_trans.
Qed.    

Lemma plus_leb_compat_l n m p:
  leb m n = true ->
  leb (p + m) (p + n) = true.
Proof.
  intro. apply leb_iff. apply plus_le_compat. apply le_refl. apply leb_iff. assumption.
Qed.

Lemma leb_plus_l n m:
  leb n (n + m) = true.
Proof.
  intros. apply leb_iff. apply le_plus_l.
Qed.

Lemma leb_plus_r n m:
  leb n (m + n) = true.
Proof.
  intros. apply leb_iff. apply le_plus_r.
Qed.

Lemma leb_refl n :
  leb n n = true.
Proof.
  intros. apply leb_iff. apply NPeano.Nat.le_refl.
Qed.

Lemma beq_nat_leb n m:
  beq_nat m n = true ->
  leb n m = true.
Proof.
  intros. apply beq_nat_true in H. subst. apply leb_refl.
Qed.

Lemma leb_true_beq_false_minus n m:
  beq_nat n m = false ->
  leb n m = true ->
  (0 < (m - n))%nat.
Proof.
  intros. apply beq_nat_false in H. apply leb_iff in H0.
  apply lt_minus_O_lt. apply le_lt_eq_dec in H0. inversion H0. assumption. tryfalse.
Qed.

Open Scope nat.
Lemma le_not_eq_lt: forall (n m : nat),
  n <> m ->
  n <= m ->
  n < m.
Proof.
  intros. apply le_lt_eq_dec in H0. inversion H0. assumption. tryfalse.
Qed.


Lemma leb_n_m_0 n m:
  leb n 0 = true ->
  leb n m = true.
Proof.
  intros. rewrite leb_iff. rewrite leb_iff in H.  apply le_n_0_eq in H. subst. apply le_0_n.
Qed.  

Lemma leb_n_plus_m_true n m:
  leb n (n+m) = true.
Proof.
  apply leb_iff. omega.
Qed.

Lemma delay_trace_n_m n m tr :
  n <= m ->
  (delay_trace n tr) m = tr (m-n).
Proof.
  intros. unfold delay_trace.
  apply leb_iff in H. rewrite H. reflexivity.
Qed.

Theorem Contr_translation_sound: forall (c : Contr) (il_e : ILExpr) (envC : Env' Val) (extC : ExtEnv' Val)
                                        (envIL : Env' ILVal) (extIL : ExtEnv' ILVal) (envILtrans : Env' ILExpr)
                                        (v' : ILVal) trace rv p1 p2 t0 curr,
  (forall a a', Asset.eqb a a' = true) -> (* look a bit wierd but I'm just saying that I treat all the assest the same *)
  (forall l t, extC l t = translateILVal (extIL l t)) ->
  fromContr envILtrans c t0 = Some il_e ->
  (C[|c|] envC (adv_ext (Z.of_nat t0) extC)) = Some trace ->
  (forall t, trace t p1 p2 curr = rv) -> (* this is the most problematic place *)
  IL[|il_e|] envIL extIL p1 p2 = Some v'->
  RVal rv = translateILVal v'.
Proof.
  intro c. induction c. Focus 5.
  + intros. simpl in *. option_inv_auto. rewrite adv_ext_iter in H6.  rewrite of_nat_plus in H6.
    (*rewrite delay_trace_iter.*)    
    eapply IHc with (envC := envC).
    eassumption. eassumption. eassumption.
    rewrite plus_comm. apply H6. intros. rewrite <- (H3 (n+t)). unfold delay_trace. rewrite leb_n_plus_m_true.
    replace (n + t -n) with t. reflexivity. omega. eassumption.

  + intros. simpl in *. some_inv. subst. simpl in *. some_inv. (*erewrite <- H3.*) compute. unfold compose in H2. some_inv.
    erewrite <- H3.  reflexivity.
  + intros. simpl in *. option_inv_auto. eapply IHc; try (eassumption).
  + intros. simpl in *. some_inv. subst. erewrite <- (H3 0). compute.
    destruct (Party.eqb p p0).
    - simpl in *. some_inv. subst. destruct t0; reflexivity.
    - simpl in *. some_inv. unfold eval_payoff. destruct (Party.eqb p p1); destruct (Party.eqb p0 p2); try (rewrite H; reflexivity);
      simpl; destruct (Party.eqb p p2); destruct (Party.eqb p0 p1); simpl; try (rewrite H; reflexivity); reflexivity.
  + intros. simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
    destruct_vals. some_inv. subst. unfold scale_trace, compose, scale_trans in H3.
    
      erewrite <- H3. rewrite Rmult_comm. apply translateILVal_RVal_f_eq.
    - eapply Exp_translation_sound; try (simpl in *; some_inv; subst); try eassumption.
    - eapply IHc with (envC := envC) (trace := x0) (curr := curr); try eassumption. intros.
      (* And I'm stuck. Should be reflexivity, but existential variable can't be instantiated with
                't' because 't' was introduces after application of 'erewrite <- H3' above*)
      instantiate (1:=0). admit. (* need to instantiate with something just to make admit tactics work *)
      
      (*reflexivity.
      intros. unfold liftM, compose, bind. rewrite H3. unfold pure.
      reflexivity. rewrite Equivalence.delay_trace_at. reflexivity.*)
  + intros. simpl in *. option_inv_auto. unfold pure in H9. some_inv. subst. simpl in *.
    option_inv_auto. destruct_vals. some_inv. erewrite <- H3. unfold add_trace, add_trans. 
    apply translateILVal_RVal_f_eq. eapply IHc1; try eassumption. (* stuck again, for the same reason as in previos case *)

(* Bunch of other attempts *)
(*
 Theorem Contr_translation_sound: forall (c : Contr) (il_e : ILExpr) (envC : Env' Val) (extC : ExtEnv' Val)
                                        (envIL : Env' ILVal) (extIL : ExtEnv' ILVal) (envILtrans : Env' ILExpr)
                                        (v' : ILVal) trace rv p1 p2 t0 t curr,
  (forall a a', Asset.eqb a a' = true) ->
  (forall l t, extC l t = translateILVal (extIL l t)) ->
  fromContr envILtrans c t0 = Some il_e ->
  liftM (delay_trace t0) (C[|c|] envC (adv_ext (Z.of_nat t0) extC)) = Some trace ->
  trace t p1 p2 curr = rv ->
  IL[|il_e|] envIL extIL p1 p2 = Some v'->
  RVal rv = translateILVal v'.
Proof.
  intro c. induction c. Focus 5.
  + intros. simpl in *. option_inv_auto.
    rewrite delay_trace_iter.
    rewrite adv_ext_iter in H3. rewrite of_nat_plus in H3.
    eapply IHc with (envC := envC) (t := t); try eassumption.
    unfold liftM, compose, bind. rewrite plus_comm. rewrite H3. unfold pure. reflexivity.
    rewrite plus_comm. reflexivity.
  
  + intros. simpl in *. some_inv. subst. simpl in *. some_inv. compute. unfold compose in H2. some_inv.
    rewrite delay_empty_trace in H4.
    rewrite delay_empty_trace. reflexivity.
  + intros. simpl in *. option_inv_auto. eapply IHc with (envC := x0 :: envC); try (eassumption);
    unfold liftM, compose, bind. erewrite H5; reflexivity. reflexivity.
  + intros. simpl in *. some_inv. subst. unfold compose in H2. some_inv. unfold delay_trace, singleton_trace.
    destruct (leb t0 t).
    destruct (Party.eqb p p0).
    - simpl in *. some_inv. subst. reflexivity.
    - simpl in *. some_inv. unfold eval_payoff. destruct (Party.eqb p p1); destruct (Party.eqb p0 p2); try (rewrite H; reflexivity);
      simpl; destruct (Party.eqb p p2); destruct (Party.eqb p0 p1); simpl; try (rewrite H; reflexivity); reflexivity.
   + intros. simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
     destruct_vals. some_inv. subst. unfold scale_trace. unfold compose. unfold scale_trans.
     rewrite Equivalence.delay_trace_at. rewrite Rmult_comm.
     apply translateILVal_RVal_f_eq.
    - eapply Exp_translation_sound; try (simpl in *; some_inv; subst); try eassumption.
    - eapply IHc with (envC := envC) (trace := delay_trace t0 x1); try eassumption. unfold liftM, compose, bind. rewrite H3. unfold pure.
      reflexivity.  unfold not. intros.
      rewrite Equivalence.delay_trace_at. reflexivity.

      + intros. simpl in *. option_inv_auto.
        rewrite Equivalence.delay_trace_at. rewrite fromContract_pushForward in H1. option_inv' H1.
        unfold delay_trace. simpl.
        rewrite adv_ext_iter in H3. rewrite of_nat_plus in H3.
        (*rewrite plus_comm in H1. rewrite fromContract_pushForward in H1. option_inv H1. subst.*)
        unfold delay_trace. simpl. simpl.
        eapply IHc with (envC := envC) (trace := delay_trace (n + t0) x0) (t0 := (n + t0)%nat).
        eassumption. eassumption. eassumption.
        unfold liftM, compose, bind. rewrite plus_comm. rewrite H3. reflexivity.
        rewrite plus_comm. rewrite Equivalence.delay_trace_at.


     simpl in *. inversion H3. option_inv_auto.
  rewrite adv_ext_iter in H5. rewrite of_nat_plus in H5.
        (*rewrite plus_comm in H1. rewrite fromContract_pushForward in H1. option_inv H1. subst.*)
        eapply IHc with (envC := envC).
        eassumption. eassumption. eassumption.
        unfold liftM, compose, bind. rewrite plus_comm. rewrite H5. reflexivity.
        intros. rewrite delay_trace_iter. rewrite plus_comm. unfold delay_trace. simpl. exists x. reflexivity.
        eassumption.
   (*----------*)
   
      destruct n.
      - simpl. eapply IHc with (envC := envC).
        eassumption. eassumption. eassumption.
        unfold liftM, compose, bind. rewrite plus_comm. rewrite H4. reflexivity.
        simpl. rewrite plus_0_r. rewrite delay_trace_0 in H3. apply H3. rewrite plus_0_r.
        rewrite Equivalence.delay_trace_at. reflexivity. eassumption.
      - simpl. eapply IHc with (envC := envC); try eassumption. unfold liftM, compose, bind. rewrite plus_comm. rewrite H4.
        rewrite delay_trace_iter. rewrite plus_comm. reflexivity.

        rewrite delay_trace_iter. rewrite Equivalence.delay_trace_at.  rewrite delay_trace_iter.
        
       rewrite plus_comm. rewrite Equivalence.delay_trace_at.
       
     rewrite plus_comm. rewrite Equivalence.delay_trace_at. rewrite <- delay_trace_iter. rewrite Equivalence.delay_trace_at.
 *)
