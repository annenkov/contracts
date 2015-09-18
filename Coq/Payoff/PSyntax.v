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
Require Import Horizon.
Require Import FunctionalExtensionality.
Require Import Days.

Import ListNotations.

Inductive ILBinOp : Set := ILAdd | ILSub | ILMult | ILDiv | ILAnd | ILOr |
                           ILLess | ILLeq | ILEqual.

Inductive ILUnOp : Set := ILNot | ILNeg.


Inductive ILExpr : Set :=
| ILIf : ILExpr -> ILExpr -> ILExpr -> ILExpr
| FloatV : R -> ILExpr
| Model : ObsLabel -> Z -> ILExpr
| ABExpr1 : ILUnOp -> ILExpr -> ILExpr
| ABExpr2 : ILBinOp -> ILExpr -> ILExpr -> ILExpr
| Payoff  : nat -> Party -> Party -> ILExpr. 

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

Definition eval_payoff disc_val p1 p2 p1' p2' :=
  if ((Party.eqb p1 p1') && (Party.eqb p2 p2')) then (ILRVal disc_val)
  else if ((Party.eqb p2 p1') && (Party.eqb p1 p2')) then (ILRVal (-disc_val))
       else (ILRVal 0).
   

Fixpoint ILsem (e : ILExpr) (env : Env' ILVal) (ext : ExtEnv' ILVal) disc p1 p2 : option ILVal:=
  match e with
    | ABExpr1 op e1 => IL[|e1|] env ext disc p1 p2 >>= fun v => ILUnOpSem op v
    | ABExpr2 op e1 e2 => IL[|e1|] env ext disc p1 p2 >>=
                            fun v1 => IL[|e2|] env ext disc p1 p2 >>=
                                        fun v2 => ILBinOpSem op v1 v2
    | ILIf b e1 e2 => match (IL[|b|] env ext disc p1 p2),(IL[|e1|] env ext disc p1 p2),(IL[|e2|] env ext disc p1 p2) with
                        | Some (ILBVal true), Some (ILRVal e1'), _ => Some (ILRVal e1')
                        | Some (ILBVal false), _,  Some (ILRVal e2') => Some (ILRVal e2')
                        | _, _, _ => None
                      end
    | FloatV v => Some (ILRVal v)
    | Model lab t => Some (ext lab t)
    | Payoff t p1' p2' => Some (eval_payoff (disc t) p1' p2' p1 p2)
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
    | Payoff t' p1 p2 => Payoff (t + t') p1 p2
  end.

Fixpoint nestedIfs (env : Env' ILExpr) (cond : ILExpr) (t' : nat) (t0 : nat)
                   (c1 : ILExpr) (c2 : ILExpr) : ILExpr :=
  match t' with
    | 0 => ILIf cond c1 c2
    | S t'' => ILIf cond c1
                    (nestedIfs env (pushForward 1 cond) t'' t0 (pushForward 1 c1) (pushForward 1 c2))                    
  end.

Fixpoint fromContr (env : Env' ILExpr) (c : Contr) (t0 : nat) : option ILExpr:=
  match c with
    | Scale e c      => fromExp env (Z.of_nat t0) e
                                >>= fun v => (fromContr env c t0)
                                               >>= fun v' => pure (ABExpr2 ILMult v v')                          
    | Translate t' c => fromContr env c (t' + t0)
    (*| If e t' c1 c2  => (fromContr env c1 t0)
                          >>= fun v1 => (fromContr env c2 (t0 + t'))
                                          >>= fun v2 => fromExp env (Z.of_nat t0) e
                                                                >>= fun e => Some (nestedIfs env e t' t0 v1 v2) *)
    | If e 0 c1 c2  => fromContr env c1 t0
                          >>= fun v1 => fromContr env c2 t0
                                          >>= fun v2 => fromExp env (Z.of_nat t0) e
                                                                >>= fun e => Some (nestedIfs env e 0 t0 v1 v2)
    | Zero           => Some (FloatV 0)
    | Let e c        => (fromExp env (Z.of_nat t0) e)
                          >>= fun v => fromContr (v :: env) c t0                          
    | Transfer p1 p2 _ => Some (if (Party.eqb p1 p2) then (FloatV 0) else (Payoff t0 p1 p2))
    | Both c1 c2     => (fromContr env c1 t0)
                          >>= fun v1 => (fromContr env c2 t0)
                                          >>= fun v2 => pure (ABExpr2 ILAdd v1 v2)
    | _ => None
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
                                          (v : Val) (v' : ILVal) p1 p2 t0 disc,
  fromExp envILtrans t0 e = Some il_e ->
  (forall l t, extC l t = translateILVal (extIL l t)) ->
  E[|e|] envC (adv_ext t0 extC) = Some v ->
  IL[|il_e|] envIL extIL disc p1 p2 = Some v'->
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

Fixpoint listFromNdesc0 (n : nat) (count : nat) : list nat := 
  match count with
    | O => []
    | S n' => n + n' :: listFromNdesc0 n n'
  end.

Example list_from_N_desc0 : (listFromNdesc0 3 2) ++  [2] = [4;3;2].
Proof.
  compute. reflexivity.
Qed.


Notation "tr1 '~+~' tr2" := (add_trans tr1 tr2) (at level 50, left associativity).

Definition sum_list xs := fold_right Rplus 0%R xs.

Definition sum_from_to n m f := sum_list (map f (listFromNdesc n m)).

Definition sampleContr1 := Both (Translate 5%nat (Scale sampleExp (Transfer P1 P2 EUR))) (Transfer P1 P2 EUR).
Eval compute in optionApp (Csem sampleContr1 [] (fun some_obs t => (RVal 20))) 5.

Lemma delay_trace_empty_before_n n tr t:
  t < n ->
  (delay_trace n tr) t = empty_trans.
Proof.
  intros. unfold delay_trace. apply leb_correct_conv in H. rewrite H. reflexivity.
Qed.

Lemma summ_of_0_is_0 t0 t f:
  (forall x, f x = 0%R) ->
  sum_from_to t0 t f = 0%R.
Proof.
  generalize dependent t0.
  induction t.
  + intros. unfold sum_from_to. simpl. unfold sum_list. compute. rewrite H. rewrite Rplus_0_r. reflexivity.
  + intros. unfold sum_from_to. simpl. rewrite H. unfold sum_list. simpl. unfold sum_from_to, sum_list in IHt.
    rewrite Rplus_0_l. rewrite IHt. reflexivity. assumption.
Qed.

Lemma sum_of_map_empty_trace : forall n n0 p1 p2 curr trace ,
  trace = empty_trace ->
  sum_list (map (fun t => trace t p1 p2 curr) (seq n0 n)) = 0%R.
Proof.
  induction n.
  + intros. reflexivity.
  + intros. simpl. rewrite IHn. rewrite H. unfold empty_trace, const_trace, empty_trans. ring. assumption.
Qed.

Lemma delay_trace_zero_before_n : forall n tr p1 p2 curr t0 f,
  sum_list (map (fun t1 : nat => (f t1 * (delay_trace (n + t0) tr t1 p1 p2 curr))%R) (seq t0 n)) = 0%R.
Proof.
  induction n.
  + intros. reflexivity.
  + intros. simpl. rewrite delay_trace_empty_before_n. unfold empty_trans. rewrite Rmult_0_r.
    rewrite Rplus_0_l. replace (S (n + t0)) with (n + S t0).
    apply IHn. omega. rewrite <- plus_Sn_m. omega.
Qed.

Lemma sum_split : forall l1 l2,
  sum_list (l1 ++ l2) = ((sum_list l1) + (sum_list l2))%R.
Proof.
  induction l1.
  + intros. destruct l2.
    - simpl. rewrite Rplus_0_l. reflexivity.
    - simpl. rewrite Rplus_0_l. reflexivity.
  + intros. simpl. rewrite IHl1. rewrite Rplus_assoc. reflexivity.
Qed.

Lemma seq_split : forall n t0 t,
  seq t0 (n + t) = seq t0 n ++ seq (t0 + n) t.
Proof.
  intro n. induction n.
  + intros. rewrite plus_0_l. rewrite plus_0_r. reflexivity.
  + intros. simpl. apply f_equal. rewrite IHn. replace (t0 + S n) with (S t0 + n). reflexivity.
    omega.
Qed.

Lemma sum_delay t0 t n tr p1 p2 curr f:
  sum_list (map (fun t => (f t * (delay_trace (n + t0) tr) t p1 p2 curr)%R) (seq t0 (n + t))) =
  sum_list (map (fun t => (f t * (delay_trace (n + t0) tr) t p1 p2 curr)%R) (seq (t0+n) t)).
Proof.
  rewrite seq_split. rewrite map_app. rewrite sum_split. rewrite delay_trace_zero_before_n. rewrite Rplus_0_l. reflexivity.
Qed.

Check liftM.
Check sum_from_to 0 1.

Lemma zero_horizon_empty_trans c t trace env ext:
  horizon c = 0 ->
  C[|c|] env ext = Some trace ->
  trace t = empty_trans.
Proof.
  intros. eapply horizon_sound with (c := c). rewrite H. omega. eassumption.
Qed.

Lemma zero_horizon_empty_trace c trace env ext:
  horizon c = 0 ->
  C[|c|] env ext = Some trace ->
  trace = empty_trace.
Proof.
  intros. apply functional_extensionality. intros. eapply horizon_sound with (c := c). rewrite H. omega. eassumption.
Qed.

Lemma zero_horizon_delay_trace c m trace env ext:
  horizon c = 0 ->
  C[|c|] env ext = Some trace ->
  delay_trace m trace = trace.
Proof.
  intros. apply functional_extensionality. intros. unfold delay_trace. destruct (leb m x).
  - erewrite zero_horizon_empty_trans. erewrite zero_horizon_empty_trans. reflexivity. eassumption. eassumption. eassumption.
    eassumption.
  - erewrite zero_horizon_empty_trans. reflexivity. eassumption. eassumption.
Qed.
  
Lemma sum_list_zero_horizon : forall n c t env ext trace p1 p2 curr f,
  horizon c = 0 ->
  C[|c|] env ext = Some trace ->
  sum_list (map (fun t => (f t * trace t p1 p2 curr)%R) (seq t n)) = 0%R.
Proof.
  induction n.
  + intros. reflexivity.
  + intros. simpl. erewrite IHn. erewrite zero_horizon_empty_trans. unfold empty_trans. ring.
    eassumption. eassumption. eassumption. eassumption.
Qed.

Lemma summ_list_common_factor: forall n f x t0 g,
  sum_list (map (fun t : nat => (g t * (f t * x)))%R (seq t0 n)) =
  (x * sum_list (map (fun t : nat => (g t * f t))%R  (seq t0 n)))%R.
Proof.
  induction n.
  + intros. simpl. ring.
  + intros. simpl. rewrite IHn. ring.
Qed.

Fixpoint R_times_nat (r : R) (n : nat) :=
  match n with
    | O => 0%R
    | S n' => (r + R_times_nat r n')%R
  end.

Lemma summ_list_plus: forall n f g t0 q,
  sum_list (map (fun t : nat => (q t * (f t + g t)))%R (seq t0 n)) =
  (sum_list (map (fun t : nat => (q t * f t)) (seq t0 n)) + sum_list (map (fun t : nat => (q t * g t)) (seq t0 n)))%R.
Proof.
  induction n.
  + intros. simpl. ring.
  + intros. simpl. rewrite IHn. rewrite <- Rplus_assoc. ring. 
Qed.

Lemma sum_after_horizon_zero : forall n t0 c trace p1 p2 curr ext env,
  C[|c|] env ext = Some trace ->                               
  sum_list (map (fun t => trace t p1 p2 curr) (seq (t0 + horizon c) n)) = 0%R.
Proof.
  intros n.
  induction n.
  + intros. reflexivity.
  + intros. simpl. erewrite horizon_sound. unfold empty_trans.
    rewrite <- plus_Sn_m. erewrite IHn. ring.
    eassumption. instantiate (1:=c). omega. eassumption.
Qed.

Lemma sum_delay_after_horizon_zero : forall n m t0 c trace p1 p2 curr ext env f,
  m <= t0 ->
  C[|c|] env ext = Some trace ->                               
  sum_list (map (fun t => (f t * delay_trace m trace t p1 p2 curr)%R) (seq (t0 + horizon c) n)) = 0%R.
Proof.
  intros n.
  induction n.
  + intros. reflexivity.
  + intros. simpl. rewrite delay_trace_n_m. erewrite horizon_sound. unfold empty_trans.
    rewrite <- plus_Sn_m. erewrite IHn. ring. omega. eassumption.
    instantiate (1:=c). omega. eassumption. omega.
Qed.

Lemma sum_before_after_horizon t0 t c trace p1 p2 curr ext env f:
  C[|c|] env ext = Some trace ->
  sum_list (map (fun t => (f t * (delay_trace t0 trace) t p1 p2 curr))%R (seq t0 (horizon c + t))) =
  sum_list (map (fun t => (f t * (delay_trace t0 trace) t p1 p2 curr))%R (seq t0 (horizon c))).
Proof.
  intros. rewrite seq_split. rewrite map_app. rewrite sum_split. erewrite sum_delay_after_horizon_zero. ring.
  omega. eassumption.
Qed.

Lemma delay_add_trace n tr1 tr2:
      add_trace (delay_trace n tr1) (delay_trace n tr2) = delay_trace n (add_trace tr1 tr2).
Proof.
  unfold add_trace, delay_trace, compose. apply functional_extensionality. intros. destruct (leb n x).
  - reflexivity.
  - rewrite add_empty_trans_l. reflexivity.
Qed.


Lemma map_delay_trace : forall n m t0 x0 p1 p2 curr,
  m <= t0 ->
  map (fun t : nat => delay_trace m x0 t p1 p2 curr) (seq t0 n) =
  map (fun t : nat => x0 (t-m) p1 p2 curr) (seq t0 n).
Proof.
  induction n.
  - reflexivity.
  - intros. simpl. rewrite delay_trace_n_m. apply f_equal. apply IHn. omega. omega.
Qed.  

Ltac destruct_option_vals := repeat (match goal with
                        | [x : match ?X : option Val with _ => _ end = _ |- _] => destruct X; tryfalse
                        | [x : match ?X : option ILVal with _ => _ end = _ |- _]  => destruct X; tryfalse
                      end).

Ltac destruct_option_vals_in H := match H with
                        | [match ?X : option Val with _ => _ end = _ ] => destruct X; tryfalse
                        | [match ?X : option ILVal with _ => _ end = _ ]  => destruct X; tryfalse
                      end.



Theorem Contr_translation_sound: forall (c : Contr) (il_e : ILExpr) (envC : Env' Val) (extC : ExtEnv' Val)
                                        (envIL : Env' ILVal) (extIL : ExtEnv' ILVal) (envILtrans : Env' ILExpr)
                                        (v' : ILVal) p1 p2 t0 curr v trace disc,
  (forall a a', Asset.eqb a a' = true) -> (* looks a bit weird but I'm just saying that I treat all the assests the same *)
  (forall l t, extC l t = translateILVal (extIL l t)) ->
  fromContr envILtrans c t0 = Some il_e ->
  (C[|Translate t0 c|] envC extC) = Some trace ->
  sum_list (map (fun t => (disc t * trace t p1 p2 curr)%R) (seq t0 (horizon c))) = v ->
  IL[|il_e|] envIL extIL disc p1 p2 = Some v'->
  RVal v = translateILVal v'.
Proof.
  intro c. induction c. Focus 5.
  + (* Translate *)
    intros. simpl in *.
    option_inv_auto. rewrite adv_ext_iter in H3. rewrite of_nat_plus in H3. rewrite delay_trace_iter.
    eapply IHc with (envC := envC); try eassumption.
    unfold liftM, compose, bind.
    rewrite plus_comm. rewrite H3. reflexivity. rewrite plus_comm.
    assert (Hseq:(seq (n + t0)) = (seq (t0 + n))). rewrite plus_comm. reflexivity. rewrite Hseq.
    rewrite <- sum_delay. destruct (horizon c) eqn:Hhor.
    - simpl. eapply sum_list_zero_horizon with (c:=c). assumption.
      erewrite zero_horizon_delay_trace. eassumption. eassumption. eassumption.
    - unfold plus0. reflexivity.
  + (* Zero *)
    intros. simpl in *. some_inv. subst. simpl in *. some_inv. compute. unfold compose in H2. some_inv.
    reflexivity.
  + (* Let *)
    intros. simpl in *. option_inv_auto. eapply IHc with (envC := (x0 :: envC)); try eassumption. unfold liftM, compose, bind.
    rewrite H5. unfold pure. reflexivity. reflexivity.
  + (* Transfer *)
    intros. simpl in *. some_inv. subst. rewrite Rplus_0_r. unfold compose in H2. some_inv.
    rewrite Equivalence.delay_trace_at. unfold singleton_trace, singleton_trans.
    destruct (Party.eqb p p0).
    - simpl in *. some_inv. subst. rewrite Rmult_0_r. destruct t0; reflexivity. 
    - simpl in *. some_inv. unfold eval_payoff. destruct (Party.eqb p p1); destruct (Party.eqb p0 p2);
      try (rewrite H; rewrite Rmult_1_r; reflexivity);
      simpl; destruct (Party.eqb p p2); destruct (Party.eqb p0 p1); simpl; try (rewrite H); try (apply f_equal; ring); reflexivity.
  + (* Scale *)
    intros. simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
    destruct_vals. some_inv. subst. rewrite <- delay_scale_trace. unfold scale_trace, compose, scale_trans.
    rewrite summ_list_common_factor.  apply translateILVal_RVal_f_eq.
    - eapply Exp_translation_sound; try (simpl in *; some_inv; subst); try eassumption.
    - eapply IHc with (envC := envC) (curr := curr); try eassumption. unfold liftM, compose, bind. rewrite H3. reflexivity. reflexivity.
  + (* Both *)
    intros. simpl in *. option_inv_auto. unfold pure in H8. some_inv. subst. simpl in *. option_inv_auto. destruct_vals. some_inv.
    rewrite <- delay_add_trace. unfold add_trace, add_trans. rewrite summ_list_plus.
    apply translateILVal_RVal_f_eq.
    - eapply IHc1 with (envC:=envC); try eassumption. unfold liftM, compose, bind. rewrite H2. reflexivity.
      destruct (Max.max_dec (horizon c1) (horizon c2)) as [Hmax_h1 | Hmax_h2].
      * rewrite Hmax_h1. reflexivity.
      * rewrite Hmax_h2. apply NPeano.Nat.max_r_iff in Hmax_h2. assert (Hh2eq: horizon c2 = horizon c1 + (horizon c2 - horizon c1)). omega.
        rewrite Hh2eq. erewrite sum_before_after_horizon. reflexivity. eassumption.
    - eapply IHc2 with (envC:=envC); try eassumption. unfold liftM, compose, bind. rewrite H3. reflexivity.
      destruct (Max.max_dec (horizon c1) (horizon c2)) as [Hmax_h1 | Hmax_h2].
      * rewrite Hmax_h1. apply NPeano.Nat.max_l_iff in Hmax_h1. assert (Hh2eq: horizon c1 = horizon c2 + (horizon c1 - horizon c2)). omega.
        rewrite Hh2eq. erewrite sum_before_after_horizon. reflexivity. eassumption.
      * rewrite Hmax_h2. reflexivity.
  + (* If *)
    intros. simpl in *. option_inv_auto.
    generalize dependent t0.
    induction n.
    - (* n = 0 *)
      intros. simpl in *. destruct (fromExp envILtrans (Z.of_nat t0) e) eqn:Hfromexp; tryfalse.
      option_inv_auto. simpl in *.
      destruct (IL[|x2|] envIL extIL disc p1 p2) eqn:Hil_bool; tryfalse.
      (* Condition evaluates to true *)
      destruct i; tryfalse. destruct b. destruct (E[|e|] envC (adv_ext (Z.of_nat t0) extC)) eqn: Hexp; tryfalse.
      replace v with (translateILVal (ILBVal true)) in H6. simpl in H6.
      destruct (IL[|x0|] envIL extIL disc p1 p2) eqn: Hil_r; tryfalse.
      destruct_option_vals; some_inv.
      eapply IHc1 with (envC:=envC); try eassumption. unfold liftM, compose, bind. rewrite H6.
      reflexivity. rewrite plus0_0_n.
      destruct (Max.max_dec (horizon c1) (horizon c2)) as [Hmax_h1 | Hmax_h2].
        rewrite Hmax_h1. reflexivity.
        rewrite Hmax_h2. apply NPeano.Nat.max_r_iff in Hmax_h2. assert (Hh2eq: horizon c2 = horizon c1 + (horizon c2 - horizon c1)). omega.
        rewrite Hh2eq. erewrite sum_before_after_horizon. reflexivity. eassumption.
      symmetry. eapply Exp_translation_sound; try eassumption.

      (* Condition evaluates to false *)
      (* rewrite plus_0_r in H2 *)
      destruct (E[|e|] envC (adv_ext (Z.of_nat t0) extC)) eqn: Hexp; tryfalse.
      replace v with (translateILVal (ILBVal false)) in H6. simpl in H6.
      destruct (IL[|x1|] envIL extIL disc p1 p2) eqn: Hil_r; tryfalse.
      destruct_option_vals; some_inv.
      eapply IHc2 with (envC:=envC); try eassumption. unfold liftM, compose, bind. rewrite H6.
      reflexivity. rewrite plus0_0_n.
      destruct (Max.max_dec (horizon c1) (horizon c2)) as [Hmax_h1 | Hmax_h2].
        rewrite Hmax_h1. apply NPeano.Nat.max_l_iff in Hmax_h1. assert (Hh2eq: horizon c1 = horizon c2 + (horizon c1 - horizon c2)). omega.
        rewrite Hh2eq. erewrite sum_before_after_horizon. reflexivity. eassumption.
        rewrite Hmax_h2. reflexivity.
      symmetry. eapply Exp_translation_sound; try eassumption. option_inv_auto.
    - (* n = S n' *) 
      intros. simpl in *. tryfalse.
      (*destruct (IL[|x2|] envIL extIL disc p1 p2) eqn:Hil_bool; tryfalse.
      (* Condition evaluates to true *)
      destruct i; tryfalse. destruct b. destruct (E[|e|] envC (adv_ext (Z.of_nat t0) extC)) eqn: Hexp; tryfalse.
      replace v with (translateILVal (ILBVal true)) in H6. simpl in H6.
      destruct (IL[|x0|] envIL extIL disc p1 p2) eqn: Hil_r; tryfalse. destruct i; tryfalse.
      destruct_option_vals; some_inv.
      eapply IHc1 with (envC:=envC); try eassumption. unfold liftM, compose, bind. rewrite H6.
      reflexivity.
      destruct (Max.max_dec (horizon c1) (horizon c2)) as [Hmax_h1 | Hmax_h2].
      rewrite Hmax_h1. destruct (horizon c1) eqn:Hhor1.
        reflexivity.
        unfold plus0. rewrite <- Hhor1. rewrite plus_comm. erewrite sum_before_after_horizon; try reflexivity; try eassumption.
      rewrite Hmax_h2. apply NPeano.Nat.max_r_iff in Hmax_h2.
      destruct (horizon c2) eqn:Hhor2.
        simpl. eapply sum_list_zero_horizon with (c:=c1). omega. erewrite zero_horizon_delay_trace with (c:=c1). eassumption. omega.
        eassumption.

        unfold plus0. rewrite <- Hhor2. assert (Hh2eq: S n + horizon c2 = horizon c1 + ((horizon c2 - horizon c1)) + S n). omega.
        rewrite Hh2eq. rewrite <- plus_assoc.
        erewrite sum_before_after_horizon. reflexivity. eassumption. tryfalse.
        
     symmetry. eapply Exp_translation_sound; try eassumption.
     (* Condition evaluates to false *)
      destruct (E[|e|] envC (adv_ext (Z.of_nat t0) extC)) eqn: Hexp; tryfalse.
      replace v with (translateILVal (ILBVal false)) in H6. simpl in H6.
      destruct (IL[|nestedIfs envILtrans (pushForward 1 x2) n t0 
               (pushForward 1 x0) (pushForward 1 x1)|] envIL extIL disc p1 p2) eqn: Hil_r; tryfalse.
      destruct_option_vals; some_inv.
      eapply IHc2 with (envC:=envC); try eassumption. unfold liftM, compose, bind.
      unfold liftM, compose, bind in H6. rewrite H6.
      reflexivity. rewrite plus0_0_n.
      destruct (Max.max_dec (horizon c1) (horizon c2)) as [Hmax_h1 | Hmax_h2].
        rewrite Hmax_h1. apply NPeano.Nat.max_l_iff in Hmax_h1. assert (Hh2eq: horizon c1 = horizon c2 + (horizon c1 - horizon c2)). omega.
        rewrite Hh2eq. erewrite sum_before_after_horizon. reflexivity. eassumption.
        rewrite Hmax_h2. reflexivity.
     symmetry. eapply Exp_translation_sound; try eassumption. *)
Qed.
