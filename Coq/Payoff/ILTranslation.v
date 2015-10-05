Add LoadPath "..".

Require Import Tactics.
Require Import ILSyntax.
Require Import ILSemantics.
Require Import Denotational.
Require Import Equivalence.
Require Import Syntax.
Require Import Utils.
Require Import Horizon.
Require Import Days.
Require Import Misc.

Require Import List.
Require Import ZArith.
Require Import FunctionalExtensionality.

Import ListNotations.

Fixpoint fromExp (t0 : Z) (e : Exp) :=
  match e with
    | OpE Add [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILAdd v1 v2)))
    | OpE Sub [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILSub v1 v2)))
    | OpE Mult [a1;a2] => (fromExp t0 a1) >>= fun v1 =>
                             (fromExp t0 a2) >>= fun v2 => pure (ILBinExpr ILMult v1 v2)
    | OpE Div [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILDiv v1 v2)))
    | OpE And [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILAnd v1 v2)))
    | OpE Or [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILOr v1 v2)))
    | OpE Less [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILLess v1 v2)))
    | OpE Leq [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILLeq v1 v2)))
    | OpE Equal [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILEqual v1 v2)))
    | OpE (RLit v) _ => Some (FloatV v)
    | OpE _ _ => None
    | Obs lab t => Some (Model lab (t0 + t))
    | VarE n => None
    | Acc _ _ _ => None
  end.

Fixpoint pushForward (t : nat) (e : ILExpr) : ILExpr :=
  match e with
    | ILIf b e1 e2 => ILIf (pushForward t b) (pushForward t e1) (pushForward t e2)
    | Model s t' => Model s (Z.add (Z.of_nat t) t')
    | ILUnExpr op e1 => ILUnExpr op (pushForward t e1)
    | ILBinExpr op e1 e2 => ILBinExpr op (pushForward t e1) (pushForward t e2)
    | FloatV v => FloatV v
    | Payoff t' p1 p2 => Payoff (t + t') p1 p2
  end.

Fixpoint nestedIfs (cond : ILExpr) (t' : nat)
                   (c1 : ILExpr) (c2 : ILExpr) : ILExpr :=
  match t' with
    | 0 => ILIf cond c1 c2
    | S t'' => ILIf cond c1
                    (nestedIfs (pushForward 1 cond) t'' (pushForward 1 c1) (pushForward 1 c2))
  end.

Fixpoint fromContr (c : Contr) (t0 : nat) : option ILExpr:=
  match c with
    | Scale e c      => fromExp (Z.of_nat t0) e
                                >>= fun v => (fromContr c t0)
                                               >>= fun v' => pure (ILBinExpr ILMult v v')                          
    | Translate t' c => fromContr c (t' + t0)
    | If e t' c1 c2  => (fromContr c1 t0)
                          >>= fun v1 => (fromContr c2 t0)
                                          >>= fun v2 => fromExp (Z.of_nat t0) e
                                                                >>= fun e => Some (nestedIfs e t' v1 v2)
    | Zero           => Some (FloatV 0)
    | Let e c        => None
    | Transfer p1 p2 _ => Some (if (Party.eqb p1 p2) then (FloatV 0) else (Payoff t0 p1 p2))
    | Both c1 c2     => (fromContr c1 t0)
                          >>= fun v1 => (fromContr c2 t0)
                                          >>= fun v2 => pure (ILBinExpr ILAdd v1 v2)
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


Ltac destruct_vals := repeat (match goal with
                        | [x : Val |- _] => destruct x; tryfalse
                        | [x : ILVal |- _] => destruct x; tryfalse
                              end).

Ltac some_inv := repeat (unfold pure in *; match goal with
                   | [H: Some _ = Some _ |- _] => inversion H; clear H
                 end).

Theorem Exp_translation_sound : forall (e : Exp) (il_e : ILExpr) (envC : Env' Val) (extC : ExtEnv' Val)
                                          (envIL : Env' ILVal) (extIL : ExtEnv' ILVal)
                                          (v : Val) (v' : ILVal) p1 p2 t0 disc,
  fromExp t0 e = Some il_e ->
  (forall l t, extC l t = translateILVal (extIL l t)) ->
  E[|e|] envC (adv_ext t0 extC) = Some v ->
  IL[|il_e|] envIL extIL disc p1 p2 = Some v'->
  v = translateILVal v'.
Proof.
  intros. generalize dependent envC. generalize dependent extC.
  generalize dependent envIL. generalize dependent extIL.
  generalize dependent il_e. generalize dependent v. generalize dependent v'.

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

Lemma delay_scale_trace tr t n :
  scale_trace n (delay_trace t tr) = delay_trace t (scale_trace n tr).
Proof.
  unfold scale_trace, delay_trace, compose. apply functional_extensionality. intros. destruct (leb t x).
  - reflexivity.
  - apply scale_empty_trans.
Qed.

Local Open Scope nat.

Lemma delay_trace_n_m n m tr :
  n <= m ->
  (delay_trace n tr) m = tr (m-n).
Proof.
  intros. unfold delay_trace.
  apply leb_iff in H. rewrite H. reflexivity.
Qed.

Lemma delay_trace_empty_before_n n tr t:
  t < n ->
  (delay_trace n tr) t = empty_trans.
Proof.
  intros. unfold delay_trace. apply leb_correct_conv in H. rewrite H. reflexivity.
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

Lemma sum_delay t0 t n tr p1 p2 curr f:
  sum_list (map (fun t => (f t * (delay_trace (n + t0) tr) t p1 p2 curr)%R) (seq t0 (n + t))) =
  sum_list (map (fun t => (f t * (delay_trace (n + t0) tr) t p1 p2 curr)%R) (seq (t0+n) t)).
Proof.
  rewrite seq_split. rewrite map_app. rewrite sum_split. rewrite delay_trace_zero_before_n. rewrite Rplus_0_l. reflexivity.
Qed.

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

Definition translation_sound c envC extC t0 := forall (il_e : ILExpr)
                                        (envIL : Env' ILVal) (extIL : ExtEnv' ILVal)
                                        (v' : ILVal) p1 p2 curr v trace disc,
  (forall a a', Asset.eqb a a' = true) ->
  (forall l t, extC l t = translateILVal (extIL l t)) ->
  fromContr c t0 = Some il_e ->
  C[|Translate t0 c|] envC extC = Some trace ->
  sum_list (map (fun t => (disc t * trace t p1 p2 curr)%R) (seq t0 (horizon c))) = v ->
  (IL[|il_e|] envIL extIL) disc p1 p2 = Some v'->
  RVal v = translateILVal v'.

Fixpoint unrollIfWithin e :=
  match e with
    | If b O c1 c2 as If0 => If0
    | If b (S n) c1 c2 => If b 0 c1 (If b n c1 c2)
    | e' => e'
  end.

Check fromExp.

Lemma push_forward_expr : forall e t0,
  liftM (pushForward 1) (fromExp t0 e) = fromExp (Z.succ t0) e.
Proof.  
  induction e using Exp_ind'; intros; try reflexivity.
   - intros. simpl.
    destruct op; repeat (destruct args; try reflexivity);
    unfold liftM, compose, bind; apply all_to_forall2 in H; inversion_clear H;
    erewrite <- H0; erewrite <- H1; destruct (fromExp t0 e);  destruct (fromExp t0 e0); try reflexivity.
   - unfold liftM, compose, bind. unfold fromExp. apply f_equal. unfold pushForward. apply f_equal. ring.
Qed.

Lemma push_forward_distr : forall n b e1 e2,
   pushForward 1 (nestedIfs b n e1 e2) =
   nestedIfs (pushForward 1 b) n (pushForward 1 e1) (pushForward 1 e2).
Proof.
  induction n.
  - intros. reflexivity.
  - intros. simpl. rewrite IHn. reflexivity.
Qed.  

Lemma push_forward_contr : forall c t0,
  liftM (pushForward 1) (fromContr c t0) = fromContr c (S t0).
Proof.
  induction c; intros; try reflexivity.
  - simpl. unfold compose. apply f_equal. destruct (Party.eqb p p0); try reflexivity.
  - simpl. unfold liftM, compose, bind. replace (Z.pos (Pos.of_succ_nat t0)) with (Z.succ (Z.of_nat t0)). rewrite <- push_forward_expr.
    destruct (fromExp (Z.of_nat t0) e). simpl. rewrite <- IHc. destruct (fromContr c t0); try reflexivity. unfold liftM, compose, bind.
    reflexivity. rewrite Zpos_P_of_succ_nat. reflexivity.
  - simpl. unfold liftM, compose, bind. replace (n + S t0) with (S (n + t0)). apply IHc. omega.
  - simpl. unfold liftM, compose, bind. rewrite <- IHc1. rewrite <- IHc2.
    destruct (fromContr c1 t0). destruct (fromContr c2 t0); try reflexivity.
    unfold liftM, compose, bind. reflexivity.
  - simpl. unfold liftM, compose, bind. rewrite <- IHc1. rewrite <- IHc2. unfold liftM, compose, bind, pure.
    destruct (fromContr c1 t0). destruct (fromContr c2 t0); try reflexivity.
    replace (Z.pos (Pos.of_succ_nat t0)) with (Z.succ (Z.of_nat t0)). rewrite <- push_forward_expr.
    unfold liftM, compose, bind. destruct (fromExp (Z.of_nat t0) e). simpl. apply f_equal. apply push_forward_distr. reflexivity.
    symmetry. apply Zpos_P_of_succ_nat. reflexivity.
Qed.

Theorem Contr_translation_sound: forall c envC extC t0,
  translation_sound c envC extC t0.
Proof.
  intro c. induction c;  unfold translation_sound. Focus 5.
  + (* Translate *)
    intros. simpl in *.
    option_inv_auto. rewrite adv_ext_iter in H3. rewrite of_nat_plus in H3. rewrite delay_trace_iter.
    eapply IHc with (envC := envC); try eassumption.
    unfold liftM, compose, bind. simpl.
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
    intros. tryfalse.
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
    - eapply IHc with (envC := envC) (curr := curr); try eassumption. unfold liftM, compose, bind. simpl.
      rewrite H3. reflexivity. reflexivity.
  + (* Both *)
    intros. simpl in *. option_inv_auto. unfold pure in H8. some_inv. subst. simpl in *. option_inv_auto. destruct_vals. some_inv.
    rewrite <- delay_add_trace. unfold add_trace, add_trans. rewrite summ_list_plus.
    apply translateILVal_RVal_f_eq.
    - eapply IHc1 with (envC:=envC); try eassumption. unfold liftM, compose, bind. simpl. rewrite H2. reflexivity.
      destruct (Max.max_dec (horizon c1) (horizon c2)) as [Hmax_h1 | Hmax_h2].
      * rewrite Hmax_h1. reflexivity.
      * rewrite Hmax_h2. apply NPeano.Nat.max_r_iff in Hmax_h2. assert (Hh2eq: horizon c2 = horizon c1 + (horizon c2 - horizon c1)). omega.
        rewrite Hh2eq. erewrite sum_before_after_horizon. reflexivity. eassumption.
    - eapply IHc2 with (envC:=envC); try eassumption. unfold liftM, compose, bind. simpl. rewrite H3. reflexivity.
      destruct (Max.max_dec (horizon c1) (horizon c2)) as [Hmax_h1 | Hmax_h2].
      * rewrite Hmax_h1. apply NPeano.Nat.max_l_iff in Hmax_h1. assert (Hh2eq: horizon c1 = horizon c2 + (horizon c1 - horizon c2)). omega.
        rewrite Hh2eq. erewrite sum_before_after_horizon. reflexivity. eassumption.
      * rewrite Hmax_h2. reflexivity.
  + (* If *)
    intros. simpl in *. option_inv_auto.
    generalize dependent t0. generalize dependent v'.
    generalize dependent x0. generalize dependent x1.
    generalize dependent x2. generalize dependent x.
    induction n.
    - (* n = 0 *)
      intros. simpl in *. destruct (fromExp (Z.of_nat t0) e) eqn:Hfromexp; tryfalse.
      option_inv_auto. simpl in *.
      destruct (IL[|x2|] envIL extIL disc p1 p2) eqn:Hil_bool; tryfalse.
      (* Condition evaluates to true *)
      destruct i; tryfalse. destruct b. destruct (E[|e|] envC (adv_ext (Z.of_nat t0) extC)) eqn: Hexp; tryfalse.
      replace v with (translateILVal (ILBVal true)) in H6. simpl in H6.
      destruct (IL[|x0|] envIL extIL disc p1 p2) eqn: Hil_r; tryfalse.
      destruct_option_vals; some_inv.
      eapply IHc1 with (envC:=envC); try eassumption. unfold liftM, compose, bind. simpl. rewrite H6.
      reflexivity. rewrite plus0_0_n.
      destruct (Max.max_dec (horizon c1) (horizon c2)) as [Hmax_h1 | Hmax_h2].
        rewrite Hmax_h1. reflexivity.
        rewrite Hmax_h2. apply NPeano.Nat.max_r_iff in Hmax_h2. assert (Hh2eq: horizon c2 = horizon c1 + (horizon c2 - horizon c1)). omega.
        rewrite Hh2eq. erewrite sum_before_after_horizon. reflexivity. eassumption.
      symmetry. eapply Exp_translation_sound; try eassumption.

      (* Condition evaluates to false *)
      destruct (E[|e|] envC (adv_ext (Z.of_nat t0) extC)) eqn: Hexp; tryfalse.
      replace v with (translateILVal (ILBVal false)) in H6. simpl in H6.
      destruct (IL[|x1|] envIL extIL disc p1 p2) eqn: Hil_r; tryfalse.
      destruct_option_vals; some_inv.
      eapply IHc2 with (envC:=envC); try eassumption. unfold liftM, compose, bind. simpl. rewrite H6.
      reflexivity. rewrite plus0_0_n.
      destruct (Max.max_dec (horizon c1) (horizon c2)) as [Hmax_h1 | Hmax_h2].
        rewrite Hmax_h1. apply NPeano.Nat.max_l_iff in Hmax_h1. assert (Hh2eq: horizon c1 = horizon c2 + (horizon c1 - horizon c2)). omega.
        rewrite Hh2eq. erewrite sum_before_after_horizon. reflexivity. eassumption.
        rewrite Hmax_h2. reflexivity.
      symmetry. eapply Exp_translation_sound; try eassumption.
    - (* n = S n' *) 
      intros. simpl in *. tryfalse.
      destruct (IL[|x2|] envIL extIL disc p1 p2) eqn:Hil_bool; tryfalse.
      (* Condition evaluates to true *)
      destruct i; tryfalse. destruct b. destruct (E[|e|] envC (adv_ext (Z.of_nat t0) extC)) eqn: Hexp; tryfalse.
      replace v with (translateILVal (ILBVal true)) in H6. simpl in H6.
      destruct (IL[|x0|] envIL extIL disc p1 p2) eqn: Hil_r; tryfalse. destruct i; tryfalse.
      destruct_option_vals; some_inv.
      eapply IHc1 with (envC:=envC); try eassumption. unfold liftM, compose, bind. simpl. rewrite H6.
      reflexivity.
      destruct (Max.max_dec (horizon c1) (horizon c2)) as [Hmax_h1 | Hmax_h2].
      (* max = horizon c1 *)
        rewrite Hmax_h1. destruct (horizon c1) eqn:Hhor1.
        reflexivity.
        unfold plus0. rewrite <- Hhor1. rewrite plus_comm. erewrite sum_before_after_horizon; try reflexivity; try eassumption.
      (* max = horizon c2 *)
        rewrite Hmax_h2. apply NPeano.Nat.max_r_iff in Hmax_h2.
        destruct (horizon c2) eqn:Hhor2.
        simpl. eapply sum_list_zero_horizon with (c:=c1). omega. erewrite zero_horizon_delay_trace with (c:=c1). eassumption. omega.
        eassumption.

        unfold plus0. rewrite <- Hhor2. assert (Hh2eq: S n + horizon c2 = horizon c1 + ((horizon c2 - horizon c1)) + S n). omega.
        rewrite Hh2eq. rewrite <- plus_assoc.
        erewrite sum_before_after_horizon. reflexivity. eassumption. tryfalse.
        
     symmetry. eapply Exp_translation_sound; try eassumption.
     (* Condition evaluates to false *)
     destruct (max (horizon c1) (horizon c2)) eqn:Hmax. simpl in *.
     Focus 2.
     unfold plus0. unfold plus0 in IHn. rewrite <- Hmax. rewrite <- Hmax in IHn.
     destruct (Max.max_dec (horizon c1) (horizon c2)) as [Hmax_h1 | Hmax_h2]. simpl.
     (* max = horizon c1 *)
     rewrite Hmax_h1. rewrite Hmax_h1 in IHn. 
     destruct (E[|e|] envC (adv_ext (Z.of_nat t0) extC)) eqn: Hexp; tryfalse.
     replace v with (translateILVal (ILBVal false)) in H6. simpl in H6.
     unfold liftM, bind, compose in H6. rewrite adv_ext_iter in H6.
     destruct (IL[|nestedIfs (pushForward 1 x2) n
                             (pushForward 1 x0) (pushForward 1 x1)|] envIL extIL disc p1 p2) eqn:Hil_if; tryfalse. destruct i; tryfalse.
     some_inv. 
     
     destruct (within_sem C[|c1|] C[|c2|] e n envC (adv_ext (Z.of_nat t0 + 1) extC)) eqn:Hwithin; tryfalse. some_inv. subst.
     rewrite Equivalence.delay_trace_at. rewrite delay_trace_empty_before_n. unfold empty_trans. rewrite Rmult_0_r. rewrite Rplus_0_l.
     rewrite delay_trace_iter. replace (1 + t0) with (S t0).
     eapply IHn.
     replace (Z.of_nat t0 + 1)%Z with (Z.of_nat(S t0)) in Hwithin. eassumption. rewrite of_nat_succ. reflexivity.
     rewrite of_nat_succ. eassumption.
     rewrite <- push_forward_contr. rewrite H3. unfold liftM, compose, bind. reflexivity.
     rewrite <- push_forward_contr. rewrite H2. unfold liftM, compose, bind. reflexivity.
     rewrite Nat2Z.inj_succ. rewrite <- push_forward_expr. rewrite H5. unfold liftM, compose, bind. reflexivity. omega. omega.
     symmetry. eapply Exp_translation_sound; try eassumption.

     (* max = horizon c2 *)
     rewrite Hmax_h2. rewrite Hmax_h2 in IHn. simpl.
     destruct (E[|e|] envC (adv_ext (Z.of_nat t0) extC)) eqn: Hexp; tryfalse.
     replace v with (translateILVal (ILBVal false)) in H6. simpl in H6.
     unfold liftM, bind, compose in H6. rewrite adv_ext_iter in H6.
     destruct (IL[|nestedIfs (pushForward 1 x2) n
                             (pushForward 1 x0) (pushForward 1 x1)|] envIL extIL disc p1 p2) eqn:Hil_if; tryfalse. destruct i; tryfalse.
     some_inv.
     destruct (within_sem C[|c1|] C[|c2|] e n envC (adv_ext (Z.of_nat t0 + 1) extC)) eqn:Hwithin; tryfalse. some_inv. subst.
     rewrite Equivalence.delay_trace_at. rewrite delay_trace_empty_before_n. unfold empty_trans. rewrite Rmult_0_r. rewrite Rplus_0_l.
     rewrite delay_trace_iter. replace (1 + t0) with (S t0).
     eapply IHn.
     replace (Z.of_nat t0 + 1)%Z with (Z.of_nat(S t0)) in Hwithin. eassumption. rewrite of_nat_succ. reflexivity.
     rewrite of_nat_succ. eassumption.
     rewrite <- push_forward_contr. rewrite H3. unfold liftM, compose, bind. reflexivity.
     rewrite <- push_forward_contr. rewrite H2. unfold liftM, compose, bind. reflexivity.
     rewrite Nat2Z.inj_succ. rewrite <- push_forward_expr. rewrite H5. unfold liftM, compose, bind. reflexivity. omega. omega.
     symmetry. eapply Exp_translation_sound; try eassumption.


     (* max = 0*)
     destruct (E[|e|] envC (adv_ext (Z.of_nat t0) extC)) eqn: Hexp; tryfalse.
     replace v with (translateILVal (ILBVal false)) in H6. simpl in H6.
     unfold liftM, bind, compose in H6. rewrite adv_ext_iter in H6.
     destruct (IL[|nestedIfs (pushForward 1 x2) n
                             (pushForward 1 x0) (pushForward 1 x1)|] envIL extIL disc p1 p2) eqn:Hil_if; tryfalse. destruct i; tryfalse.
     some_inv. 
     
     destruct (within_sem C[|c1|] C[|c2|] e n envC (adv_ext (Z.of_nat t0 + 1) extC)) eqn:Hwithin; tryfalse. some_inv. subst.     
     eapply IHn.
     replace (Z.of_nat t0 + 1)%Z with (Z.of_nat(S t0)) in Hwithin. eassumption. rewrite of_nat_succ. reflexivity.
     rewrite of_nat_succ. eassumption.
     rewrite <- push_forward_contr. rewrite H3. unfold liftM, compose, bind. reflexivity.
     rewrite <- push_forward_contr. rewrite H2. unfold liftM, compose, bind. reflexivity.
     rewrite Nat2Z.inj_succ. rewrite <- push_forward_expr. rewrite H5. unfold liftM, compose, bind. reflexivity.
     symmetry. eapply Exp_translation_sound; try eassumption.
Qed.
