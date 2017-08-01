(* Add LoadPath "..". *)

Require Import Tactics.
Require Import ILSyntax.
Require Import ILSemantics.
Require Import Denotational.
Require Import Syntax.
Require Import Utils.
Require Import Horizon.
Require Import Misc.
Require Import Reduction.
Require Import Typing.
Require Import Templates.
Require Import ILTranslation.

Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import FunctionalExtensionality.
Require Import Coq.Program.Equality.

Import ListNotations.

Open Scope nat.
Import Nat.

Fixpoint cutPayoff (e : ILExpr) : ILExpr :=
  match e with
    | ILIf b e1 e2 => ILIf b (cutPayoff e1) (cutPayoff e2)
    | ILModel s t' => ILModel s t'
    | ILUnExpr op e1 => ILUnExpr op (cutPayoff e1)
    | ILBinExpr op e1 e2 => ILBinExpr op (cutPayoff e1) (cutPayoff e2)
    | ILLoopIf cond e1 e2 t => ILLoopIf cond (cutPayoff e1) (cutPayoff e2) t
    | ILFloat v => ILFloat v
    | ILNat v => ILNat v
    | ILtexpr t => ILtexpr t
    | ILBool b => ILBool b
    | ILNow => ILNow
    | ILPayoff t' p1 p2 => ILIf (ILBinExpr ILLessN (ILtexpr t') ILNow) (ILFloat 0%R) (ILPayoff t' p1 p2)
  end.

(*Semantic equvivalence of IL expressions*)

Definition ILequiv t_now tenv e1 e2 :=
  forall ext t0 disc p1 p2, IL[|e1|] ext tenv t0 t_now disc p1 p2 = IL[|e2|]ext tenv t0 t_now disc p1 p2.

Notation "e1 '~~[' t_now ',' tenv ']' e2" := (ILequiv t_now tenv e1 e2) (at level 50).

Lemma cutPayoff_eq_compiled_expr e e_il t0: fromExp t0 e = Some e_il -> e_il = cutPayoff e_il.
Proof.
  generalize dependent t0. generalize dependent e_il.
  induction e using Exp_ind'; intros; tryfalse.
  - simpl in *. destruct op;
    (* Binary operations *)
    simpl in *; do 3 try (destruct args; tryfalse); tryfalse; simpl in *;
         option_inv_auto; subst; simpl in *; try some_inv; subst; simpl in *;
         destruct_vals; subst; option_inv_auto;
         try (apply all_to_forall2 in H; inversion_clear H as [He1 He2];
              erewrite <- He1; eauto; erewrite <- He2; eauto; reflexivity);
    (* Unary operations*)
         try (apply all_to_forall1 in H; erewrite <- H; eauto; reflexivity); try reflexivity.
    (* Cond *)
    simpl in *. do 4 try (destruct args; tryfalse); tryfalse; simpl in *;
    eapply all_to_forall3 in H; inversion_clear H as [IHe1 IHe']; inversion_clear IHe' as [IHe2 IHe3];
    option_inv_auto; subst; simpl in *; try some_inv; subst.
    simpl in *. erewrite <- IHe2;eauto. erewrite <- IHe3;eauto.
  - simpl in *. some_inv. reflexivity.
Qed.

Lemma ltb_plus_l_false n1 n2 n3:
  Nat.ltb n1 n2 = false ->
  Nat.ltb (n3 + n1) n2 = false.
Proof.
  intros. apply not_true_is_false. apply not_true_iff_false in H. unfold not in *. intros. apply Nat.ltb_lt in H0.
  apply H. apply ltb_lt.  omega.
Qed.

Lemma ltb_plus_both_false n1 n2 n3:
  ltb n1 n2 = false -> ltb (n3 + n1) (n3 + n2) = false.
Proof.
  intros. apply not_true_is_false. apply not_true_iff_false in H. unfold not in *. intros. apply ltb_lt in H0.
  apply H. apply ltb_lt.  omega.
Qed.

Lemma ILexpr_eq_cutPayoff_at_zero e tenv: e ~~[0,tenv] cutPayoff e.
Proof.
  (*generalize dependent tenv.*)
  induction e; intros; simpl in *; unfold ILequiv; try reflexivity.
  - intros. simpl. unfold bind,compose,pure.
    remember (IL[|e1|] ext tenv t0 0%nat disc p1 p2) as ILv1.
    destruct ILv1; tryfalse; try reflexivity. destruct i; try reflexivity. destruct b. apply IHe2. apply IHe3.
  - intros. simpl. unfold bind,compose,pure. rewrite IHe. reflexivity.
  - intros. simpl. unfold bind,compose,pure. rewrite IHe1. rewrite IHe2. reflexivity.
  - intros. simpl.
    generalize dependent t1.
    induction (TexprSem t0 tenv).
    + intros; simpl. rewrite IHe1. rewrite IHe2. rewrite IHe3. reflexivity.
    + intros; simpl. unfold bind,compose,pure. rewrite IHe1. rewrite IHe2.
      destruct (IL[|cutPayoff e1|] ext tenv t1 0%nat disc p1 p2); try reflexivity. destruct i; try reflexivity.
      destruct b; try reflexivity. apply IHn.
Qed.

Hint Resolve cutPayoff_eq_compiled_expr.

Require Import Arith.Compare_dec.
Lemma ILexpr_eq_cutPayoff_at_n e tenv c t0 n t_now:
  fromContr c t0 = Some e ->
  ILTexprSem t0 tenv = n ->
  ltb n t_now = false ->
  e ~~[t_now,tenv] cutPayoff e.
Proof.
  intros. generalize dependent e. generalize dependent t0. generalize dependent n.
  induction c; intros; simpl in H; tryfalse; some_inv; subst; unfold ILequiv; intros.
  - reflexivity.
  - simpl in *. some_inv. unfold eval_payoff. destruct (Party.eqb p p0); simpl; try reflexivity. (* unfold tenv_update at 3.*)
    simpl. rewrite ltb_plus_l_false; eauto.
  - option_inv_auto. some_inv. subst. simpl. unfold bind,compose,pure.
    replace (cutPayoff x) with x by eauto. rewrite <- IHc with (n:=(ILTexprSem t0 tenv)) (t0:=t0). reflexivity.
    assumption. reflexivity. assumption.
  - unfold ILequiv in IHc.
    replace match t0 with
        | Tvar _ =>
            match t1 with
            | ILTexpr (Tnum 0) => ILTexpr t0
            | _ => ILTplus (ILTexpr t0) t1
            end
        | Tnum 0 => t1
        | Tnum (S _) =>
            match t1 with
            | ILTexpr (Tnum 0) => ILTexpr t0
            | _ => ILTplus (ILTexpr t0) t1
            end
        end with (tsmartPlus (ILTexpr t0) t1) in H by reflexivity.
    eapply IHc with (t0:=(tsmartPlus' (ILTexpr t0) t1)) (n:=ILTexprSem (tsmartPlus' (ILTexpr t0) t1) tenv).
    simpl. rewrite fold_unfold_ILTexprSem'. rewrite tsmartPlus_sound'. simpl. apply not_true_is_false. unfold not. intros.
    apply ltb_lt in H0. apply not_true_iff_false in H1. unfold not in H1.
    rewrite ltb_lt in H1. apply H1. omega. reflexivity.
    assumption.
  - option_inv_auto. some_inv. subst. simpl. unfold bind,compose,pure. erewrite <- IHc1; eauto. erewrite <- IHc2; eauto.
  - option_inv_auto. some_inv. subst. simpl. unfold bind,compose,pure.
    generalize dependent t2.
    induction (TexprSem t0 tenv); intros.
    + simpl. unfold bind,compose,pure. erewrite <- IHc1; eauto. erewrite <- IHc2; eauto.
    + simpl. unfold bind,compose,pure. erewrite <- IHc1; eauto. simpl in *.
      destruct (IL[|x1|] ext tenv t2 t_now disc p1 p2); try reflexivity.
      destruct i; try reflexivity. destruct b.
      * reflexivity.
      * simpl. rewrite IHn. reflexivity.
Qed.

Lemma horizon_smartScale_eq c e' tenv:
  isZeroLit e' = false ->
  horizon c tenv = horizon (smartScale e' c) tenv.
Proof.
  intros. unfold smartScale. rewrite H. destruct c; reflexivity.
Qed.

Lemma horizon_gt_0_smartScale c e' tenv:
  0 < horizon (smartScale e' c) tenv ->
  horizon c tenv = horizon (smartScale e' c) tenv.
Proof.
  generalize dependent e'.
  induction c; intros; simpl; unfold smartScale;
  try (destruct (isZeroLit e') eqn:HisZ; unfold smartScale in H; try (rewrite HisZ in *); simpl in *; inversion H; reflexivity).
Qed.

(*Lemma exp_not_zero_smartScale c e' tenv:
  0 < horizon (smartScale e' c) tenv ->
  horizon c tenv = horizon (smartScale e' c) tenv.
Proof.
  generalize dependent e'.
  induction c; intros; simpl; unfold smartScale;
  try (destruct (isZeroLit e') eqn:HisZ; unfold smartScale in H; try (rewrite HisZ in ; simpl in *; inversion H; reflexivity).
Qed.*)

Lemma horizon_eq_0_smartScale c e' tenv:
  horizon c tenv = 0->
  horizon (smartScale e' c) tenv = 0.
Proof.
  generalize dependent e'.
  induction c; intros; simpl in *; unfold smartScale; destruct (isZeroLit e') eqn:HisZ; tryfalse; simpl; try reflexivity; auto.
Qed.

Hint Resolve ext_inst_typed env_inst_typed.

Hint Constructors Red.

Lemma horizon_smartBoth c1 c2 tenv:
  horizon (Both c1 c2) tenv = horizon (smartBoth c1 c2) tenv.
Proof.
  simpl. destruct c1; simpl; try reflexivity; destruct c2; try (rewrite Max.max_0_r); try reflexivity.
Qed.

Check within_sem.

Lemma cutPayoff_ILsem_at_n : forall tenv t_now e n extIL disc p1 p2,
  t_now <= n ->
  IL[|cutPayoff e|] extIL tenv n t_now disc p1 p2 = IL[|e|] extIL tenv n t_now disc p1 p2.
Proof.
  induction e; simpl; auto.
  - intros; unfold liftM,compose,bind,pure. rewrite <- IHe1; auto. rewrite <- IHe2; auto. rewrite <- IHe3; auto.
  - rename t0 into t.
    induction (TexprSem t tenv).
    + intros; simpl. rewrite <- IHe1; auto. rewrite <- IHe2; auto. rewrite <- IHe3; auto.
    + intros; simpl. rewrite <- IHe1; auto. rewrite <- IHe2. rewrite IHn; auto. auto.
  - intros. rewrite plus_comm. rewrite ltb_plus_l_false. reflexivity.
    apply not_true_is_false. unfold not. intros.
    apply ltb_lt in H0. simpl in *. omega.
Qed.

Lemma cutPayoff_ILsem_at_n' : forall nn tenv t_now e1 e2 cond n extIL disc p1 p2,
  t_now <= S n ->
  IL[|cond|] extIL tenv n t_now disc p1 p2 = Some (ILBVal false) ->
  IL[|cutPayoff (ILLoopIf cond e1 e2 (Tnum (S nn)))|] extIL tenv n t_now disc p1 p2 =
  IL[|ILLoopIf cond e1 e2 (Tnum (S nn))|] extIL tenv n t_now disc p1 p2.
Proof.
  intros. simpl. unfold liftM,compose,bind,pure. rewrite H0.
  generalize dependent t_now. generalize dependent e1. generalize dependent e2. generalize dependent cond.
  generalize dependent n.
  - induction nn.
    + intros; simpl. unfold liftM,compose,bind,pure. rewrite cutPayoff_ILsem_at_n;eauto. rewrite cutPayoff_ILsem_at_n;eauto.
    + intros; simpl. unfold liftM,compose,bind,pure. cases (IL[|cond|] extIL tenv (S n) t_now disc p1 p2); try reflexivity.
      cases i; try reflexivity. cases b.
      * rewrite cutPayoff_ILsem_at_n; eauto.
      * rewrite IHnn; eauto.
Qed.


Theorem cutPayoff_sound_one_step c c' envC extC:
  forall (il_e : ILExpr) (extIL : ExtEnv' ILVal) (envP : EnvP) (extP : ExtEnvP)
         (v' : ILVal) p1 p2 curr v trace (disc : nat -> R ) tenv tr g,
  (forall a a', Asset.eqb a a' = true) ->
  (forall l t, fromVal (extC l t) = extIL l t) ->
  fromContr c (ILTexpr (Tnum 0)) = Some il_e ->
  Red c envP extP c' tr ->
  C[|c'|] envC (adv_ext 1 extC) tenv = Some trace ->
  sum_list (map (fun t => (disc (1+t)%nat * trace t p1 p2 curr)%R)
                (seq 0 (horizon c' tenv))) = v ->
  IL[|cutPayoff il_e|] extIL tenv 0 1 disc p1 p2 = Some v'->
  TypeExt extC ->
  TypeEnv g envC ->
  g |-C c ->
  ext_inst extP extC ->
  env_inst envP envC ->
  fromVal (RVal v) = v'.
Proof.
  intros until g. intros A Xeq TC R Cs S ILs Tx Te T J I.
  generalize dependent il_e. generalize dependent extIL.
  generalize dependent trace. (*generalize dependent old_trace.*) generalize dependent disc.
  generalize dependent tenv. generalize dependent v. generalize dependent v'.
  induction R.
  - (* red_zero *)intros. simpl in *. some_inv. subst. simpl in *. unfold compose,bind,pure in *. some_inv. reflexivity.
  - (* red_let *)
    intros. simpl in *.
    option_inv_auto.
  - (* red_transf *)
    intros. simpl in *. option_inv_auto. simpl in *. some_inv. subst.
    destruct (Party.eqb c p0).
    + simpl in *. some_inv. reflexivity.
    + simpl in *. some_inv. reflexivity.
  - (* red_scale *)
    intros. subst. simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
    destruct_vals. some_inv. subst.
    inversion T. unfold smartScale in Cs.
    cases (isZeroLit (TranslateExp.translateExp (-1) (specialiseExp e env ext))) as Zerolit.
    + simpl in *. some_inv. rewrite sum_of_map_empty_trace.
      assert (E[|TranslateExp.translateExp (-1) (specialiseExp e env ext)|] envC (adv_ext 1 extC) = Some (RVal 0)) as Hexp.
      rewrite isZeroLit_true with (x:=TranslateExp.translateExp (-1) (specialiseExp e env ext)). reflexivity. eassumption.
      symmetry. apply ILRVal_zero_mult_l. symmetry.
      erewrite <- cutPayoff_eq_compiled_expr in H2. try eassumption.

      rewrite TranslateExp.translateExp_ext in Hexp.
      erewrite specialiseExp_sound in Hexp; try (rewrite adv_ext_iter; simpl; rewrite adv_ext_0); try assumption.
      rewrite <- fromVal_RVal_eq.
      eapply Exp_translation_sound with (envC:=envC);
      try (simpl in *; some_inv; subst); try eassumption. simpl.
      rewrite adv_ext_iter in Hexp. simpl in *. eassumption.
      eassumption. assumption. eassumption. reflexivity.
    + erewrite <- cutPayoff_eq_compiled_expr in H2; try eassumption.
      replace (match c' with
                 | Zero => Zero
                 | _ => Scale (TranslateExp.translateExp (-1) (specialiseExp e env ext)) c'
               end) with (smartScale (TranslateExp.translateExp (-1) (specialiseExp e env ext)) c') in Cs.
      erewrite smartScale_sound in Cs; eauto.
      simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
      destruct_vals. some_inv. subst. unfold scale_trace, compose, scale_trans.
      rewrite summ_list_common_factor. rewrite <- fromVal_RVal_eq. apply fromVal_RVal_f_eq.
      * eapply Exp_translation_sound; try (simpl in *; some_inv; subst); try eassumption. simpl.
        rewrite TranslateExp.translateExp_ext in H4.
        erewrite specialiseExp_sound in H4; eauto; try (rewrite adv_ext_iter in H4; simpl; rewrite adv_ext_0 in H4);
        try (rewrite adv_ext_iter; simpl; rewrite adv_ext_0); eauto.
      * eapply IHR; eauto. rewrite <- horizon_smartScale_eq. reflexivity. assumption.
      * constructor. apply TranslateExp.translateExp_type; eauto. eapply Preservation.red_typed; eauto.
      * unfold smartScale. rewrite Zerolit. reflexivity.
  - (*red_trans0 *)
    intros. inversion T. simpl in *. option_inv_auto. eapply IHR; eauto.
  - (*red_transS *)
    intros. inversion T.
    subst. simpl in *. option_inv_auto.

    eapply Contr_translation_sound with (envC:=envC) (tenv:=tenv); eauto; try reflexivity. simpl.
    unfold liftM,compose,bind,pure. erewrite adv_ext_iter in H0. instantiate (2:=0).

    replace (Z.pos (Pos.of_succ_nat (n + 0 + 0))) with (1 + Z.of_nat n)%Z. rewrite H0. reflexivity.
    rewrite Zpos_P_of_succ_nat. replace (n + 0 + 0) with n by omega. omega.
    simpl. replace (n + 0 + 0) with n by omega.
    rewrite <- Nat.add_1_l. rewrite plus_comm. replace (n + 1) with (n + 1 + 0) by omega.
    rewrite <- sum_delay.
    replace (n + 1 + horizon c tenv) with (S (n + horizon c tenv)) by omega. simpl.
    erewrite Soundness.red_sound1 with (t:=empty_trans) (c:=Translate (Tnum (S n)) c); eauto.
    unfold empty_trans. rewrite Rmult_0_r. rewrite Rplus_0_l.
    destruct (horizon c tenv) eqn:Hhor.
    + simpl. eapply sum_list_zero_horizon with (c:=c). eassumption.
      erewrite zero_horizon_delay_trace; eassumption.
    + unfold plus0. replace (n + 1 + 0) with (n + 1) by omega.
      rewrite plus_comm. replace 1 with (0 + 1) at 1 by reflexivity.
      rewrite sum_delay'. simpl.  reflexivity.
    + simpl. instantiate (1:=tenv). unfold liftM,compose,bind,pure.
      replace (Z.pos (Pos.of_succ_nat n)) with (1 + Z.of_nat n)%Z. rewrite adv_ext_iter in H0. rewrite H0.
      replace (n + 1 + 0) with (S n) by omega. reflexivity. rewrite Zpos_P_of_succ_nat. omega.
    + rewrite <- ILs. eapply ILexpr_eq_cutPayoff_at_n; try eassumption. reflexivity. simpl.
      apply not_true_is_false. unfold not. intros. apply ltb_lt in H. omega.
  - (*red_both *)
    intros. inversion T.
    simpl in *.  option_inv_auto. some_inv. subst. erewrite smartBoth_sound in Cs; eauto.
    simpl in *. option_inv_auto. destruct_vals. some_inv. rewrite <- horizon_smartBoth. simpl.
    unfold add_trace, add_trans. rewrite summ_list_plus. rewrite <- fromVal_RVal_eq.
    apply fromVal_RVal_f_eq.
    + eapply IHR1; try eassumption.
      destruct (Max.max_dec (horizon c1' tenv) (horizon c2' tenv)) as [Hmax_h1 | Hmax_h2].
      * rewrite Hmax_h1. reflexivity.
      * rewrite Hmax_h2. apply Nat.max_r_iff in Hmax_h2.
        assert (Hh2eq: horizon c2' tenv =
                       (horizon c1' tenv) + (horizon c2' tenv - horizon c1' tenv)). omega.
        rewrite Hh2eq. replace x1 with (delay_trace 0 x1) by apply delay_trace_0.
        erewrite sum_before_after_horizon with (t1:=0). reflexivity. eassumption.
    + eapply IHR2; try eassumption.
      destruct (Max.max_dec (horizon c1' tenv) (horizon c2' tenv)) as [Hmax_h1 | Hmax_h2].
      * rewrite Hmax_h1. apply Nat.max_l_iff in Hmax_h1.
        assert (Hh2eq: (horizon c1' tenv) =
                       (horizon c2' tenv) + ((horizon c1' tenv) - (horizon c2' tenv))). omega.
        rewrite Hh2eq. replace x2 with (delay_trace 0 x2) by apply delay_trace_0.
        erewrite sum_before_after_horizon with (t1:=0). reflexivity. eassumption.
      * rewrite Hmax_h2. reflexivity.
    + constructor. eapply Preservation.red_typed. eauto. eauto. apply H4. eassumption.
      eapply Preservation.red_typed. eauto. eauto. apply H5. eassumption.
  - (* red_if0_false *)
    intros. inversion T.
    simpl in *. option_inv_auto. simpl in *. option_inv_auto.
    unfold fromBLit in H.
    cases (specialiseExp b env ext); tryfalse. cases op; tryfalse. destruct args; tryfalse. some_inv. subst.
    replace x2 with (fromVal (BVal false)) in H5. simpl in H5.
    eapply IHR; eauto. eapply Exp_translation_sound with (envC:=envC) (extC:=extC); try eassumption. simpl. rewrite adv_ext_0.
    erewrite <- specialiseExp_sound with (envp:=env) (extp:=ext) (ext:=extC); eauto. erewrite Eq. simpl. reflexivity.
  - (* red_ifS_false *)
    intros. inversion T.
    eapply Contr_translation_sound with (t0':=O) (envC := envC) (tenv:=tenv); eauto. simpl.
    simpl in *. option_inv_auto. simpl in *. option_inv_auto. unfold liftM,compose,bind,pure.
    erewrite <- specialiseExp_sound; eauto.
    rewrite Esem_fromBLit with (r:=false); eauto. rewrite adv_ext_0.
    rewrite Cs. reflexivity.

    simpl. rewrite delay_trace_0. rewrite <- S. subst. simpl.
    cases (max (horizon c1 tenv) (horizon c2 tenv)) as Hmax.
    + reflexivity.
    + unfold plus0. rewrite <- Hmax.
      destruct (Max.max_dec (horizon c1 tenv) (horizon c2 tenv)) as [Hmax_h1 | Hmax_h2].
      * rewrite Hmax_h1. simpl.
        erewrite Soundness.red_sound1 with (t:=empty_trans) (c:=If b (Tnum (S n)) c1 c2); eauto.
        unfold empty_trans. rewrite Rmult_0_r. rewrite Rplus_0_l. replace 1 with (0 + 1) at 1 by reflexivity.
        rewrite sum_delay'. simpl. rewrite delay_trace_0.  reflexivity. simpl. erewrite <- specialiseExp_sound; eauto.
        rewrite Esem_fromBLit with (r:=false); eauto. unfold liftM,compose,bind,pure. simpl in *.
        instantiate (1:= tenv). rewrite Cs. reflexivity.
      * rewrite Hmax_h2. simpl.
        erewrite Soundness.red_sound1 with (t:=empty_trans) (c:=If b (Tnum (S n)) c1 c2); eauto.
        unfold empty_trans. rewrite Rmult_0_r. rewrite Rplus_0_l. replace 1 with (0 + 1) at 1 by reflexivity.
        rewrite sum_delay'. simpl. rewrite delay_trace_0.  reflexivity. simpl. erewrite <- specialiseExp_sound; eauto.
        rewrite Esem_fromBLit with (r:=false); eauto. unfold liftM,compose,bind,pure. simpl in *.
        instantiate (1:= tenv). rewrite Cs. reflexivity.
    + intros. rewrite <- ILs. simpl in *. option_inv_auto. symmetry.
      apply cutPayoff_ILsem_at_n'; eauto. simpl in *. option_inv_auto. simpl in *. option_inv_auto. simpl in *.
      assert (fromVal (BVal false) = x2).
      eapply Exp_translation_sound with (envC:=envC) (extC:=extC); try eassumption.
      erewrite <- specialiseExp_sound with (envp:=env) (extp:=ext) (ext:=extC); eauto.
      rewrite Esem_fromBLit with (r:=false); eauto. simpl in *. rewrite H0 in *. assumption.
  - (* red_if_true *)
    intros. inversion T.
    simpl in *. option_inv_auto. simpl in *. option_inv_auto.
    destruct (TexprSem n tenv).
    + unfold loop_if_sem in *. option_inv_auto. simpl in *.
      unfold fromBLit in H.
      cases (specialiseExp b env ext); tryfalse. cases op; tryfalse. destruct args; tryfalse. some_inv. subst.
      replace x2 with (fromVal (BVal true)) in H5. simpl in H5.
      eapply IHR; eauto. eapply Exp_translation_sound with (envC:=envC) (extC:=extC); try eassumption. simpl. rewrite adv_ext_0.
      erewrite <- specialiseExp_sound with (envp:=env) (extp:=ext) (ext:=extC); eauto. erewrite Eq. simpl. reflexivity.
    + unfold loop_if_sem in *. option_inv_auto. simpl in *.
      unfold fromBLit in H.
      cases (specialiseExp b env ext); tryfalse. cases op; tryfalse. destruct args; tryfalse. some_inv. subst.
      replace x2 with (fromVal (BVal true)) in H5. simpl in H5.
      eapply IHR; eauto. eapply Exp_translation_sound with (envC:=envC) (extC:=extC); try eassumption. simpl. rewrite adv_ext_0.
      erewrite <- specialiseExp_sound with (envp:=env) (extp:=ext) (ext:=extC); eauto. erewrite Eq. simpl. reflexivity.
Qed.

Lemma smartBoth_cases c1 c2 c:
  c = smartBoth c1 c2 ->
  (c1 = Zero /\ c = c2) \/ (c = c1 /\ c2 = Zero) \/ c = Both c1 c2.
Proof.
  intros. destruct c1; destruct c2; eauto.
Qed.

Lemma fromContr_smartBoth_eq c1 c2 il_e il_e' extIL tenv disc p1 p2 t0 t r r':
  fromContr (smartBoth c1 c2) t0 = Some il_e ->
  fromContr (Both c1 c2) t0 = Some il_e' ->
  IL[|il_e|]extIL tenv 0 t disc p1 p2 = Some (ILRVal r) ->
  IL[|il_e'|]extIL tenv 0 t disc p1 p2 = Some (ILRVal r') ->
  r = r'.
Proof.
  intros. remember (smartBoth c1 c2) as sb. apply smartBoth_cases in Heqsb.
  inversion_clear Heqsb.
  - inversion H3. subst. simpl in *. rewrite H in H0. option_inv_auto. some_inv. simpl. unfold compose,bind,pure. subst. simpl in *.
    option_inv_auto. some_inv. destruct x0; tryfalse. some_inv. subst. rewrite H4 in H1. some_inv. ring.
  - inversion H3.
    + inversion H4. subst. simpl in *. rewrite H in H0. option_inv_auto. some_inv. simpl. unfold compose,bind,pure. subst. simpl in *.
      option_inv_auto. some_inv. destruct x0; tryfalse. some_inv. subst. rewrite H5 in H1. some_inv. ring.
    + subst. rewrite H in H0. some_inv. subst. rewrite H1 in H2. some_inv. auto.
Qed.

Lemma fromContr_smartBoth_eq_exists c1 c2 il_e extIL tenv disc p1 p2 t0 t r:
  fromContr (smartBoth c1 c2) t0 = Some il_e ->
  IL[|il_e|]extIL tenv 0 t disc p1 p2 = Some (ILRVal r) ->
  exists il_e', fromContr (Both c1 c2) t0 = Some il_e' /\ IL[|il_e'|]extIL tenv 0 t disc p1 p2 = Some (ILRVal r).
Proof.
  intros. remember (smartBoth c1 c2) as sb. apply smartBoth_cases in Heqsb.
  inversion_clear Heqsb.
  - inversion H1. subst. simpl in *. rewrite H. unfold compose,bind,pure. eexists. split. reflexivity. simpl. unfold compose,bind,pure.
    rewrite H0. rewrite Rplus_0_l. reflexivity.
  - inversion H1.
    + inversion H2. subst. simpl in *. rewrite H. unfold compose,bind,pure. eexists. split. reflexivity. simpl. unfold compose,bind,pure.
      rewrite H0. rewrite Rplus_0_r. reflexivity.
    + subst. rewrite H. unfold compose,bind,pure. eexists. split. reflexivity. rewrite <- H0. reflexivity.
Qed.

Lemma smartScale_cases e c c':
  c = smartScale e c' ->
  isZeroLit e = false ->
  (c' = Zero /\ c = Zero) \/ c = Scale e c'.
Proof.
  intros. unfold smartScale in *. rewrite H0 in H. try destruct (isZeroLit e); eauto; cases c'; eauto.
Qed.

(*Lemma Red_fromContr_exists c c' t envp extp t0 il_e:
  Red c envp extp c' t ->
  fromContr c t0 = Some il_e ->
  exists il_e', fromContr c' t0 = Some il_e'.
Proof.
  intro Red.
  induction Red; intros; tryfalse; subst; eexists; try reflexivity.
  - subst. simpl in *. option_inv_auto. some_inv. subst. destruct c'; simpl. reflexivity.
*)
(*
Lemma fromContr_smartScale_eq_exists e c il_e extIL tenv disc p1 p2 t0 t r n0:
  (exists il_e'', fromContr c t0 = Some il_e'') ->
  fromContr (smartScale e c) t0 = Some il_e ->
  IL[|il_e|]extIL tenv n0 t disc p1 p2 = Some (ILRVal r) ->
  exists il_e', fromContr (Scale e c) t0 = Some il_e' /\ IL[|il_e'|]extIL tenv n0 t disc p1 p2 = Some (ILRVal r).
Proof.
  intros. inversion_clear H. remember (smartScale e c) as sc. apply smartScale_cases in Heqsc.
  inversion Heqsc.
  - inversion H. subst. simpl in *. eexists. some_inv. subst. simpl in *. some_inv. unfold compose,bind,pure. eauto.
    apply isZeroLit_true in H3. subst. simpl in *.
    split. rewrite H2. reflexivity. simpl. unfold compose,bind,pure.
    rewrite H0. rewrite Rplus_0_l. reflexivity.
  - inversion H1.
    + inversion H2. subst. simpl in *. rewrite H. unfold compose,bind,pure. eexists. split. reflexivity. simpl. unfold compose,bind,pure.
      rewrite H0. rewrite Rplus_0_r. reflexivity.
    + subst. rewrite H. unfold compose,bind,pure. eexists. split. reflexivity. rewrite <- H0. reflexivity.
Qed.
 *)

Lemma Esem_ILsem_eq e1 e2 il_e1 il_e2 env ext extIL disc p1 p2 n0 t tenv t0 v1 v2 w1 w2:
  (forall l t, fromVal (ext l t) = extIL l t) ->
  E[|e1|] env (adv_ext (ILTexprSemZ t0 tenv + Z.of_nat n0) ext) = Some w1 ->
  E[|e2|] env (adv_ext (ILTexprSemZ t0 tenv + Z.of_nat n0) ext) = Some w2 ->
  w1 = w2 ->
  fromExp t0 e1 = Some il_e1 ->
  fromExp t0 e2 = Some il_e2 ->
  IL[|il_e1|]extIL tenv n0 t disc p1 p2 = Some v1 ->
  IL[|il_e2|]extIL tenv n0 t disc p1 p2 = Some v2 ->
  v1 = v2.
Proof.
  intros. subst.

  erewrite <- Exp_translation_sound with (v':=v1) (e:=e1) (il_e:=il_e1); eauto.
  erewrite <- Exp_translation_sound with (v':=v2) (e:=e2) (il_e:=il_e2);eauto.
Qed.

Import TranslateExp.

Lemma specialiseExp_ILsem_sound e il_e1 il_e2 extIL disc p1 p2 n0 t tenv t0 extp envp v1 v2 ext g env ty:
  (forall l t, fromVal (ext l t) = extIL l t) ->
  g |-E e ∶ ty -> TypeEnv g env -> TypeExt (adv_ext (ILTexprSemZ t0 tenv + Z.of_nat n0) ext) ->
  ext_inst extp (adv_ext (ILTexprSemZ t0 tenv + Z.of_nat n0) ext) -> env_inst envp env ->
  fromExp t0 e = Some il_e1 ->
  fromExp t0 (specialiseExp e envp extp) = Some il_e2 ->
  IL[|il_e1|]extIL tenv n0 t disc p1 p2 = Some v1 ->
  IL[|il_e2|]extIL tenv n0 t disc p1 p2 = Some v2 ->
  v1 = v2.
Proof.
  intros Hexteq Hty TE TX X N TE1 TE2 IL1 IL2. assert (g |-E  e ∶ ty) as Hty1. assumption.
  eapply Esem_typed_total in Hty1;eauto. inversion_clear Hty1. inversion H.
  eapply Esem_ILsem_eq with (v1:=v1) (v2:=v2) (il_e1:=il_e1) (il_e2:=il_e2)
                                     (e1:=e) (e2:=specialiseExp e envp extp); eauto.
  erewrite specialiseExp_sound; eauto.
Qed.

Lemma fromExp_specialiseExp_exists e envp extp t0 il_e:
  fromExp t0 e = Some il_e ->
  exists il_e', fromExp t0 (specialiseExp e envp extp) = Some il_e'.
Proof.
  generalize dependent il_e. generalize dependent t0.
  induction e using Exp_ind'; intros; simpl in *; tryfalse.
  destruct op; intros;

  try (simpl in *; do 3 try (destruct args; tryfalse); tryfalse; simpl in *;
  option_inv_auto; subst; simpl in *; some_inv; subst; simpl in *; subst;
  apply all_to_forall2 in H; inversion_clear H; unfold default;
  destruct (isZeroLit (specialiseExp e envp extp)); eauto; cases (isZeroLit (specialiseExp e0 envp extp)); eauto;
  destruct (isOneLit (specialiseExp e envp extp)); eauto; cases (isOneLit (specialiseExp e0 envp extp)); eauto;
  unfold specialiseOpSimp; unfold bind,compose,pure; simpl;
  cases (fromLit (specialiseExp e envp extp)); cases (fromLit (specialiseExp e0 envp extp));
  simpl;
  try destruct v; try destruct v0; simpl;
  unfold compose,bind,pure; apply H0 in H2; inversion H2; apply H3 in H1; inversion H1; eexists;
  try rewrite H; try rewrite H4; reflexivity);

  (* And and Or *)
  try (simpl in *; do 3 (destruct args; tryfalse); tryfalse; simpl in *;
  option_inv_auto; subst; simpl in *; some_inv; subst; simpl in *; subst;
  apply all_to_forall2 in H; inversion_clear H; unfold default; option_inv_auto;
  unfold specialiseOpSimp; unfold bind,compose,pure; simpl;
  cases (fromBLit (specialiseExp e envp extp)); cases (fromBLit (specialiseExp e0 envp extp)); simpl;
  try destruct b; try destruct b0; simpl;
  unfold compose,bind,pure; apply H0 in H2; inversion H2; apply H3 in H1; inversion H1; eexists;
  try rewrite H; try rewrite H4; reflexivity);

  (* UnOp *)
  try (simpl in *; do 2 try (destruct args; tryfalse); tryfalse; simpl in *;
  option_inv_auto; subst; simpl in *; some_inv; subst; simpl in *; subst;
  apply all_to_forall1 in H; unfold default; option_inv_auto;
  unfold specialiseOpSimp; unfold bind,compose,pure; simpl;
  cases (fromLit (specialiseExp e envp extp));
    try destruct v; simpl;
    unfold compose,bind,pure; apply H in H2; inversion H2;
    eexists; try rewrite H; try rewrite H0; reflexivity);

  (* Lit *)
  try (simpl in *; destruct args; tryfalse; simpl in *; eexists; reflexivity).

  (* Cond *)
  simpl in *; do 4 (destruct args; tryfalse); tryfalse; simpl in *.
  option_inv_auto; subst; simpl in *; some_inv; subst; simpl in *; subst.
  apply all_to_forall3 in H. inversion_clear H. inversion_clear H4. unfold default.
  cases (fromBLit (specialiseExp e envp extp)); simpl;
  try destruct b; simpl; eauto.
  unfold compose,bind,pure; apply H0 in H2; inversion_clear H2;  apply H in H1; inversion_clear H1;
  apply H5 in H3; inversion_clear H3; eexists.
  try rewrite H4. try rewrite H1. try rewrite H2.  reflexivity.

  (* Obs *)
  unfold default. destruct (extp l i); simpl; try destruct v; simpl; eexists; reflexivity.
Qed.


Lemma ZeroLit_ILsem_sound e il_e extIL tenv envp extp disc p1 p2 t0 t n0 v env ext g ty:
  (forall l t, fromVal (ext l t) = extIL l t) ->
  g |-E e ∶ ty -> TypeEnv g env -> TypeExt (adv_ext (ILTexprSemZ t0 tenv + Z.of_nat n0) ext) ->
  ext_inst extp (adv_ext (ILTexprSemZ t0 tenv + Z.of_nat n0) ext) -> env_inst envp env ->
  specialiseExp e envp extp = OpE (RLit 0) [] ->
  fromExp t0 e = Some il_e ->
  IL[|il_e|]extIL tenv n0 t disc p1 p2 = Some v ->
  v = ILRVal 0.
Proof.
  intros. eapply specialiseExp_ILsem_sound; eauto. rewrite H5. simpl. reflexivity. reflexivity.
Qed.

(* Shift discount function n days *)

Definition adv_disc (n : nat) (disc_fun : nat -> R) : nat -> R
  := fun x => disc_fun (n + x)%nat.

Lemma ILsem_fromExpr_adv_ext: forall e il_e il_e' ext tenv t_now n disc p1 p2 n0,
  fromExp (ILTexprZ (ILTexpr (Tnum (S n)))) e = Some il_e ->
  fromExp (ILTexprZ (ILTexpr (Tnum n))) e = Some il_e' ->
  IL[|il_e|] ext tenv n0 t_now disc p1 p2 = IL[|il_e'|] (adv_ext 1 ext) tenv n0 t_now (adv_disc 1 disc) p1 p2.
Proof.
  induction e using Exp_ind'; intros; simpl in *; tryfalse.
  destruct op; intros; tryfalse;
    (* BinOp *)
  try ( simpl in *; do 3 try (destruct args; tryfalse); tryfalse; simpl in *;
       option_inv_auto; subst; simpl in *; some_inv; subst; simpl in *; subst;
       unfold compose,bind,pure;
       apply all_to_forall2 in H; inversion_clear H; try erewrite <- H0; eauto; try erewrite <- H5;eauto;
       eauto);
    (* UnOp *)
   try (simpl in *; do 2 try (destruct args; tryfalse); tryfalse; simpl in *;
       option_inv_auto; subst; simpl in *; some_inv; subst; simpl in *; subst;
       unfold compose,bind,pure;
       apply all_to_forall1 in H; try erewrite <- H; eauto;
       eauto);
   (* Lit *)
   try (simpl in *; destruct args; tryfalse; simpl in *; some_inv; reflexivity).
  (* Cond *)
  simpl in *. do 4 try (destruct args; tryfalse); tryfalse; simpl in *.
    eapply all_to_forall3 in H. inversion_clear H as [IHe1 IHe']; inversion_clear IHe' as [IHe2 IHe3].
    option_inv_auto. some_inv. subst. simpl in *. unfold bind,compose,pure. erewrite <- IHe1; eauto.
    erewrite <- IHe2;eauto. erewrite <- IHe3;eauto.
  (* Obs *)
    intros. simpl in *. some_inv. simpl. unfold adv_ext.
    replace (Z.of_nat n0 + (i + Z.pos (Pos.of_succ_nat n)))%Z with
    (1 + (Z.of_nat n0 + (i + Z.of_nat n)))%Z by (rewrite Zpos_P_of_succ_nat; omega). reflexivity.
Qed.

Open Scope nat.

Lemma ILsem_fromContr_adv_ext: forall c il_e il_e' ext tenv t_now n disc p1 p2 n0,
  IsClosedCT c ->
  fromContr c (ILTexpr (Tnum (S n))) = Some il_e ->
  fromContr c (ILTexpr (Tnum n)) = Some il_e' ->
  IL[|il_e|] ext tenv n0 t_now disc p1 p2 = IL[|il_e'|] (adv_ext 1 ext) tenv n0 t_now (adv_disc 1 disc) p1 p2.
Proof.
  induction c.
  - intros. simpl in *. some_inv. reflexivity.
  - intros. simpl in *. tryfalse.
  - intros. simpl in *. destruct (Party.eqb p p0); some_inv. reflexivity.
    simpl in *. unfold adv_disc. replace (n0 + S n) with (1 + (n0 + n)) by ring. reflexivity.
  - intros. simpl in *. option_inv_auto. some_inv. subst. simpl. unfold bind,compose,pure. inversion H.
    erewrite <- ILsem_fromExpr_adv_ext; eauto. erewrite <- IHc; eauto.
  - intros. inversion H. simpl in *. destruct t0; tryfalse. replace (n2 + S n) with (S (n2 + n)) in H0 by ring.
    eapply IHc; eauto.
  - intros. inversion H. subst. simpl in *. option_inv_auto. some_inv. subst. simpl. unfold bind,compose,pure.
    erewrite <- IHc1; eauto. erewrite <- IHc2; eauto.
  - intros. inversion H. subst. simpl in *. option_inv_auto. some_inv. subst. simpl. unfold bind,compose,pure.
    generalize dependent n0.
    induction n1.
    + intros. simpl. erewrite ILsem_fromExpr_adv_ext; eauto.
      erewrite <- IHc1 with (il_e':=x2); eauto. erewrite <- IHc2 with (il_e':=x3); eauto.
    + intros. simpl. rewrite IHn1; eauto. erewrite ILsem_fromExpr_adv_ext; eauto.
      erewrite <- IHc1 with (il_e':=x2); eauto.
Qed.

Lemma t_now_before_cutPayoff_exp: forall e t0 il_e p1 p2 tenv extIL n0,
  fromExp t0 e = Some il_e ->
  (forall disc1 disc2 t_now, IL[|il_e|] extIL tenv n0 0 disc1 p1 p2 = IL[|il_e|] extIL tenv n0 t_now disc2 p1 p2).
Proof.
  induction e using Exp_ind'; intros; simpl in *; tryfalse.
  destruct op; intros; tryfalse;
    (* BinOp *)
  try (simpl in *; do 3 try (destruct args; tryfalse); tryfalse; simpl in *;
       option_inv_auto; subst; simpl in *; some_inv; subst; simpl in *; subst;
       unfold compose,bind,pure;
       apply all_to_forall2 in H; inversion_clear H as [IH1 IH2];
       try rewrite <- IH1 with (il_e:=x) (t_now:=t_now) (t0:=t0) (disc1:=disc1);
       try rewrite <- IH2 with (il_e:=x0) (t_now:=t_now) (t0:=t0) (disc1:=disc1); eauto);

    (* UnOp *)
   try (simpl in *; do 2 try (destruct args; tryfalse); tryfalse; simpl in *;
       option_inv_auto; subst; simpl in *; some_inv; subst; simpl in *; subst; unfold compose,bind,pure;
       apply all_to_forall1 in H; try erewrite H; eauto);
   (* Lit *)
   try (simpl in *; destruct args; tryfalse; simpl in *; some_inv; reflexivity).

  (* Cond *)
  simpl in *. do 4 try (destruct args; tryfalse); tryfalse; simpl in *.
    eapply all_to_forall3 in H. inversion_clear H as [IHe1 IHe']; inversion_clear IHe' as [IHe2 IHe3].
    option_inv_auto. some_inv. subst. simpl in *. unfold bind,compose,pure.
    erewrite <- IHe1 with (il_e:=x) (t_now:=t_now) (t0:=t0) (disc1:=disc1); eauto.
      erewrite <- IHe2 with (il_e:=x0) (t_now:=t_now) (t0:=t0) (disc1:=disc1); eauto.
      erewrite <- IHe3 with (il_e:=x1) (t_now:=t_now) (t0:=t0) (disc1:=disc1);eauto.
  (* Obs *)
    intros. simpl in *. some_inv. reflexivity.
Qed.

Lemma t_now_before_cutPayoff: forall c t0 t_now il_e disc p1 p2 tenv extIL n0,
  fromContr c t0 = Some il_e ->
  IL[|il_e|] extIL tenv n0 0 disc p1 p2 = IL[|il_e|] extIL tenv n0 t_now disc p1 p2.
Proof.
  induction c; intros; simpl in *; some_inv; tryfalse; eauto.
  - simpl in *. destruct (Party.eqb p p0); some_inv; reflexivity.
  - simpl in *. option_inv_auto. some_inv. simpl. unfold bind,compose,pure.
    erewrite t_now_before_cutPayoff_exp with (il_e:=x) (t_now:=t_now); eauto;
    erewrite <- IHc with (il_e:=x0) (t_now:=t_now);eauto.
  - option_inv_auto. some_inv. simpl. erewrite <- IHc1 with (t_now:=t_now); eauto.
  - option_inv_auto. some_inv. simpl. generalize dependent n0. rename t0 into t.
    induction (TexprSem t tenv).
    + intros. simpl. erewrite t_now_before_cutPayoff_exp with (il_e:=x1) (t_now:=t_now); eauto.
     erewrite <- IHc1 with (il_e:=x) (t_now:=t_now); eauto. erewrite <- IHc2 with (il_e:=x0) (t_now:=t_now); eauto.
    + intros. simpl. rewrite IHn; eauto. erewrite t_now_before_cutPayoff_exp with (il_e:=x1) (t_now:=t_now); eauto.
      erewrite <- IHc1 with (il_e:=x) (t_now:=t_now); eauto.
Qed.

Lemma ZeroLit_translateExp e n:
  TranslateExp.translateExp n e = OpE (RLit 0) [] ->
  e = OpE (RLit 0) [].
Proof.
  induction e using Exp_ind'; intros; simpl in *; tryfalse; try destruct op; simpl in *; try (destruct args; tryfalse); eauto.
Qed.

Hint Resolve fromVal_BVal_f_eq fromVal_RVal_f_eq fromVal_BVal_f_eq'.

Lemma translateExp_ILsem: forall e t0 n v1 v2 il_e1 il_e2 disc p1 p2 t n0 tenv extIL,
  fromExp t0 e = Some il_e1 ->
  fromExp t0 (translateExp (-n) e) = Some il_e2 ->
  IL[|il_e1|]extIL tenv n0 t disc p1 p2 = Some v1 ->
  IL[|il_e2|](adv_ext n extIL) tenv n0 t disc p1 p2 = Some v2 ->
  v1 = v2.
Proof.
  induction e using Exp_ind'; simpl in *; intros; tryfalse.

  destruct op; intros;
  (*BinOp *)
    try (do 3 (destruct args; tryfalse); apply all_to_forall2 in H; inversion_clear H;
    option_inv_auto; simpl in *; option_inv_auto; some_inv; subst;
    simpl in *; option_inv_auto; destruct_vals;
    some_inv; try eapply fromVal_RVal_f_eq; try eapply fromVal_BVal_f_eq; try eapply fromVal_BVal_f_eq'; eauto);
  (* UnOp *)
    try (do 2 (destruct args; tryfalse);
    option_inv_auto; simpl in *; option_inv_auto; some_inv; subst; apply all_to_forall1 in H;
    simpl in *; option_inv_auto; some_inv; subst; destruct_vals; simpl in *; some_inv; subst;
    try eapply fromVal_RVal_un_minus_eq; try eapply fromVal_BVal_f_eq_un; eauto);

    (* Lit *)
    simpl in *; destruct args; tryfalse; simpl in *; option_inv_auto; tryfalse; subst; simpl in *; some_inv; subst; try reflexivity.

    (* cond *)
    simpl in *. do 4 try (destruct args; tryfalse); tryfalse; simpl in *;
    eapply all_to_forall3 in H; inversion_clear H as [IHe1 IHe']; inversion_clear IHe' as [IHe2 IHe3];
    option_inv_auto; subst; simpl in *; some_inv; subst.
    simpl in *; subst; option_inv_auto; subst; simpl in *. destruct x6; tryfalse.
    destruct b.
    replace x5 with (ILBVal true) in H9; simpl in H9; eauto.
    replace x5 with (ILBVal false) in H9; simpl in H9; eauto.

    (* Obs *)
     intros. some_inv. subst. simpl in *. some_inv. subst. unfold adv_ext.
     replace (n + (Z.of_nat n0 + (- n + i + ILTexprSemZ t0 tenv)))%Z with (Z.of_nat n0 + (i + ILTexprSemZ t0 tenv))%Z by ring.
     reflexivity.
Qed.

Lemma translateExp_ILsem': forall e t0 n il_e1 il_e2 disc p1 p2 t n0 tenv extIL,
  fromExp t0 e = Some il_e1 ->
  fromExp t0 (translateExp (-n) e) = Some il_e2 ->
  IL[|il_e1|]extIL tenv n0 t disc p1 p2 = IL[|il_e2|](adv_ext n extIL) tenv n0 t disc p1 p2.
Proof.
  induction e using Exp_ind'; simpl in *; intros; tryfalse.

  destruct op; intros;
  (*BinOp *)
    try (do 3 (destruct args; tryfalse); apply all_to_forall2 in H; inversion_clear H;
    option_inv_auto; simpl in *; option_inv_auto; some_inv; subst;
    simpl in *; option_inv_auto; destruct_vals;
    some_inv; try eapply fromVal_RVal_f_eq; try eapply fromVal_BVal_f_eq; try eapply fromVal_BVal_f_eq'; eauto);
  (* UnOp *)
    try (do 2 (destruct args; tryfalse);
    option_inv_auto; simpl in *; option_inv_auto; some_inv; subst; apply all_to_forall1 in H;
    simpl in *; option_inv_auto; some_inv; subst; destruct_vals; simpl in *; some_inv; subst;
    try eapply fromVal_RVal_un_minus_eq; try eapply fromVal_BVal_f_eq_un; eauto);

    (* Lit *)
    simpl in *; destruct args; tryfalse; simpl in *; option_inv_auto; tryfalse; subst; simpl in *; some_inv; subst; try reflexivity.

    (* cond *)
    simpl in *. do 4 try (destruct args; tryfalse); tryfalse; simpl in *;
    eapply all_to_forall3 in H; inversion_clear H as [IHe1 IHe']; inversion_clear IHe' as [IHe2 IHe3];
    option_inv_auto; subst; simpl in *; try (some_inv); subst.
    simpl in *; subst; option_inv_auto; subst; simpl in *. unfold compose,bind,pure.
    erewrite <- IHe1 with (il_e1:=x2);eauto. rename t1 into t.
    destruct (IL[|x2|] extIL tenv n0 t disc p1 p2); try destruct i; try reflexivity.
    destruct b; eauto.

    (* Obs *)
     intros. some_inv. subst. simpl in *. some_inv. subst. unfold adv_ext.
     replace (n + (Z.of_nat n0 + (- n + i + ILTexprSemZ t0 tenv)))%Z with (Z.of_nat n0 + (i + ILTexprSemZ t0 tenv))%Z by ring.
     reflexivity.
Qed.

(*
Fixpoint shiftILExpr n e :=
  match e with
    | ILIf e1 e2 e3 => ILIf (shiftILExpr n e1) (shiftILExpr n e2) (shiftILExpr n e3)
    | ILFloat r => ILFloat r
    | ILNat n => ILNat n
    | ILBool b => ILBool b
    | ILtexpr t => ILtexpr t
    | ILNow  => ILNow
    | ILModel l t => ILModel l (t+n)
    | ILUnExpr op e1 => shiftILExpr n e1
    | ILBinExpr op e1 e2 => ILBinExpr op (shiftILExpr n e1) (shiftILExpr n e2)
    | ILLoopIf e1 e2 e3 t => ILLoopIf (shiftILExpr n e1) (shiftILExpr n e2) (shiftILExpr n e3) t
    | ILPayoff t p1 p2 => ILPayoff t p1 p2
    end.
*)

Lemma translateExp_specialiseExp_ILsem_sound e il_e1 il_e2 extIL disc p1 p2 n0 t tenv t0 extp envp v1 v2 ext g env ty:
  (forall l t, fromVal (ext l t) = extIL l t) ->
  g |-E e ∶ ty -> TypeEnv g env -> TypeExt (adv_ext (ILTexprSemZ t0 tenv + Z.of_nat n0) ext) ->
  ext_inst extp (adv_ext (ILTexprSemZ t0 tenv + Z.of_nat n0) ext) -> env_inst envp env ->
  fromExp t0 e = Some il_e1 ->
  fromExp t0 (translateExp (-1) (specialiseExp e envp extp)) = Some il_e2 ->
  IL[|il_e1|]extIL tenv n0 t disc p1 p2 = Some v1 ->
  IL[|il_e2|](adv_ext 1 extIL) tenv n0 t disc p1 p2 = Some v2 ->
  v1 = v2.
Proof.
  intros Hexteq Hty TE TX X N TE1 TE2 IL1 IL2. assert (g |-E  e ∶ ty) as Hty1. assumption.
  assert (fromExp t0 e = Some il_e1) as TE1' by assumption. eapply fromExp_specialiseExp_exists in TE1'. inversion TE1'.
  erewrite <- translateExp_ILsem' in IL2.
  eapply Esem_typed_total in Hty1;eauto. inversion_clear Hty1. inversion H0.
  eapply Esem_ILsem_eq with (v1:=v1) (v2:=v2)
                                     (e1:=e) (e2:=specialiseExp e envp extp); eauto.
  erewrite specialiseExp_sound; eauto. eauto. eauto.
Qed.

(* Sometimes we need to limit proof of properties of IL payoff expressions
   to constructs that are used in the compiled expressions. For example,
   such constructs as ILNow and ILtexp can appear only after cutPayoff, but
   not after compiling contacts and expressions to IL payoff language.*)

Inductive IsCompiled : ILExpr -> Prop :=
| ic_ilif      : forall e1 e2 e3, IsCompiled e1 -> IsCompiled e2 -> IsCompiled e3
                           -> IsCompiled (ILIf e1 e2 e3)
| ic_ilfloat   : forall r, IsCompiled (ILFloat r)
| ic_ilbool    : forall b, IsCompiled (ILBool b)
| ic_model     : forall l t, IsCompiled (ILModel l t)
| ic_ilunexpr  : forall op e, IsCompiled e -> IsCompiled (ILUnExpr op e)
| ic_ilbinexpr : forall op e1 e2, IsCompiled e1 -> IsCompiled e2 -> IsCompiled (ILBinExpr op e1 e2)
| ic_illoopif  : forall n e1 e2 e3, IsCompiled e1 -> IsCompiled e2 -> IsCompiled e3
                           -> IsCompiled (ILLoopIf e1 e2 e3 n)
| ic_ilpayoff  : forall t p1 p2, IsCompiled (ILPayoff t p1 p2).

Hint Constructors IsCompiled.

Lemma fromExp_IsCompiled: forall e t0 il_e,
  fromExp t0 e = Some il_e -> IsCompiled il_e.
Proof.
  induction e using Exp_ind'; simpl in *; intros; tryfalse.

  destruct op; intros;
  (*BinOp *)
    try (do 3 (destruct args; tryfalse); apply all_to_forall2 in H; inversion_clear H;
    option_inv_auto; some_inv; eauto);
  (* UnOp *)
    try (do 2 (destruct args; tryfalse); apply all_to_forall1 in H;
    simpl in *; option_inv_auto; some_inv; eauto);

    (* Lit *)
    simpl in *; destruct args; tryfalse; simpl in *; some_inv; eauto.

    (* cond *)
    simpl in *. do 4 try (destruct args; tryfalse); tryfalse; simpl in *;
    eapply all_to_forall3 in H; inversion_clear H as [IHe1 IHe']; inversion_clear IHe' as [IHe2 IHe3];
    option_inv_auto; subst; simpl in *; try (some_inv); subst. eauto.

    (* Obs *)
     intros. some_inv. eauto.
Qed.

Hint Resolve fromExp_IsCompiled.

Lemma fromContr_IsCompiled: forall c t0 il_e,
  fromContr c t0 = Some il_e -> IsCompiled il_e.
Proof.
  induction c; intros; simpl in *; tryfalse; option_inv_auto; some_inv; eauto.
  destruct (Party.eqb p p0); eauto.
Qed.

Lemma ILsem_adv_ext_n: forall il_e extIL disc p1 p2 tenv n,
  IsCompiled il_e ->
  IL[|il_e|] (adv_ext (Z.of_nat 1) extIL) tenv n 0 (adv_disc 1 disc) p1 p2 = IL[|il_e|] extIL tenv (S n) 0 disc p1 p2.
Proof.
  intros. generalize dependent n.
  induction H; intros; try (simpl in *; unfold bind,compose,pure; reflexivity).
  - simpl in *; unfold bind,compose,pure. rewrite IHIsCompiled1. rewrite IHIsCompiled2. rewrite IHIsCompiled3. eauto.
  - unfold ILsem. unfold adv_ext.
    rewrite Zplus_assoc.
    replace (Z.of_nat (S n)) with (Z.of_nat 1 + Z.of_nat n)%Z.
    reflexivity. replace (Z.of_nat 1) with 1%Z by reflexivity. rewrite of_nat_succ. ring.
  - simpl in *; unfold bind,compose,pure. rewrite IHIsCompiled; eauto.
  - simpl in *; unfold bind,compose,pure. rewrite IHIsCompiled1. rewrite IHIsCompiled2. eauto.
  - generalize dependent n0. simpl.
    induction (TexprSem n tenv).
    + intros; simpl. unfold bind,compose,pure. rewrite IHIsCompiled1. rewrite IHIsCompiled2. rewrite IHIsCompiled3. eauto.
    + intros. simpl. unfold bind,compose,pure. rewrite <- IHn0.
      rewrite <- IHIsCompiled1. rewrite <- IHIsCompiled2. eauto.
Qed.

Lemma loopif_false_step: forall n e1 e2 e3 extIL disc p1 p2 tenv,
  IL[|e1|] extIL tenv 0 0 disc p1 p2 = Some (ILBVal false) ->
  IL[|ILLoopIf e1 e2 e3 (Tnum (S n))|] extIL tenv 0 0 disc p1 p2 =
  IL[|ILLoopIf e1 e2 e3 (Tnum n)|] extIL tenv 1 0 disc p1 p2.
Proof.
  intros. simpl. rewrite H. simpl. reflexivity.
Qed.

Lemma loopif_adv_ext_n: forall n e1 e2 e3 extIL disc p1 p2 tenv,
  IsCompiled e1 -> IsCompiled e2 -> IsCompiled e3 ->
  IL[|e1|] extIL tenv 0 0 disc p1 p2 = Some (ILBVal false) ->
  IL[|ILLoopIf e1 e2 e3 (Tnum (S n))|] extIL tenv 0 0 disc p1 p2 =
  IL[|ILLoopIf e1 e2 e3 (Tnum n)|] (adv_ext 1 extIL) tenv 0 0 (adv_disc 1 disc) p1 p2.
Proof.
  intros.
  rewrite loopif_false_step;eauto. symmetry. apply ILsem_adv_ext_n;eauto.
Qed.


Theorem diagram_commutes1 c c' envC extC:
  forall (il_e il_e' : ILExpr) (extIL : ExtEnv' ILVal) (envP : EnvP) (extP : ExtEnvP)
         p1 p2 (disc : nat -> R ) tenv tr g r r',
    (forall l t, fromVal (extC l t) = extIL l t) ->
    IsClosedCT c ->
    fromContr c (ILTexpr (Tnum 0)) = Some il_e ->
    TypeExt extC ->
    TypeEnv g envC ->
    g |-C c ->
    ext_inst extP extC ->
    env_inst envP envC ->
    Red c envP extP c' tr ->
    fromContr c' (ILTexpr (Tnum 0)) = Some il_e' ->
    IL[|cutPayoff il_e|] extIL tenv 0 1 disc p1 p2 = Some (ILRVal r) ->
    IL[|il_e'|] (adv_ext 1 extIL) tenv 0 0 (adv_disc 1 disc) p1 p2 = Some (ILRVal r') ->
    r = r'.
Proof.
  intros until r'. intros Hexteq HC TC Tx Te T I J Red TC'.
  generalize dependent il_e. generalize dependent il_e'. generalize dependent extIL.
  generalize dependent disc.  generalize dependent tenv.
  generalize dependent r. generalize dependent r'.
  induction Red. Focus 7.
  (* Both*)
  intros. inversion HC. inversion T. subst.
  eapply fromContr_smartBoth_eq_exists with (r:=r') in TC';eauto. inversion_clear TC'. inversion_clear H.
  simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
  destruct x; tryfalse. destruct x5; tryfalse. destruct x6; tryfalse. destruct x4;tryfalse. some_inv.
  f_equal. eapply IHRed1; eauto. eapply IHRed2; eauto.
  Focus 6.
  (* translate_S*)
  intros. inversion HC. inversion T. subst. simpl in *. erewrite <- ILexpr_eq_cutPayoff_at_n in H1; eauto.
  erewrite <- t_now_before_cutPayoff in H1;eauto.
  erewrite <- ILsem_fromContr_adv_ext with (c:=c) in H2; eauto. rewrite H2 in H1. some_inv. reflexivity.

  - intros. subst. simpl in *. some_inv. subst. simpl in *. some_inv. reflexivity.
  - intros. subst. simpl in *. tryfalse.
  - intros. subst. simpl in *. some_inv. simpl.
    destruct (Party.eqb c p0).
    + simpl in *. some_inv. subst. simpl in *. some_inv. reflexivity.
    + subst. simpl in *. some_inv. reflexivity.
  - intros. inversion HC. inversion T. subst. simpl in *. option_inv_auto. some_inv. simpl. subst. simpl in *. option_inv_auto. some_inv.
    destruct x1; tryfalse. destruct x2; tryfalse. some_inv.
    erewrite <- cutPayoff_eq_compiled_expr in H4; eauto.
    unfold smartScale in *. cases (isZeroLit (TranslateExp.translateExp (-1) (specialiseExp e env ext))) as Zerolit.
    + simpl in *. some_inv. simpl.  subst. simpl in *. some_inv.
      apply isZeroLit_true in Zerolit.
      assert (ILRVal r0 = ILRVal 0). eapply ZeroLit_ILsem_sound; eauto. simpl. rewrite adv_ext_0. eauto.
      eapply ZeroLit_translateExp; eauto. inversion H. ring.
    + replace (match c' with
                 | Zero => Zero
                 | _ => Scale (TranslateExp.translateExp (-1) (specialiseExp e env ext)) c'
               end) with (smartScale (TranslateExp.translateExp (-1) (specialiseExp e env ext)) c') in TC'
        by (unfold smartScale; rewrite Zerolit; reflexivity).
      remember (smartScale (TranslateExp.translateExp (-1) (specialiseExp e env ext)) c') as smartS.
      assert ((c' = Zero /\ smartS = Zero) \/ smartS = Scale (TranslateExp.translateExp (-1) (specialiseExp e env ext)) c') as Scases.
      apply smartScale_cases; eauto. inversion_clear Scases.
      * inversion_clear H. subst. unfold smartScale in *. rewrite Zerolit in *.
        simpl in *. some_inv. subst. simpl in *. some_inv.
        assert (r1 = 0%R). eapply IHRed;eauto. subst. ring.
      * subst. rewrite H in TC'. simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
        destruct x3; tryfalse. destruct x4; tryfalse. some_inv. subst.
        assert (ILRVal r0 = ILRVal r).
        eapply translateExp_specialiseExp_ILsem_sound with (n0:=0); eauto.  simpl. rewrite adv_ext_0. eassumption.
        erewrite <-  t_now_before_cutPayoff_exp; eauto.
        assert (r1 = r2). eauto. congruence.
  - intros. inversion HC. inversion T. subst. simpl in *. eauto.
  - intros. inversion HC. inversion T. subst. simpl in *. option_inv_auto. simpl in *. option_inv_auto. destruct_vals.
    assert (ILBVal b0 = ILBVal false). eapply specialiseExp_ILsem_sound; eauto. simpl. rewrite adv_ext_0. eassumption.
    unfold fromBLit in H. destruct (specialiseExp b env ext);tryfalse. destruct op;tryfalse. destruct args; tryfalse. some_inv.
    simpl. reflexivity. reflexivity. inversion H0. subst. eauto.
  - intros. inversion HC. inversion T. subst. simpl in *. option_inv_auto.
    assert (x = x2) by congruence. assert (x0 = x3) by congruence.
    assert (x1 = x4) by congruence. subst.
    rewrite cutPayoff_ILsem_at_n' in *; eauto.
    rewrite <- loopif_adv_ext_n in H3.
    erewrite <- t_now_before_cutPayoff with (c:=If b (Tnum (S n)) c1 c2) (t0:=(ILTexpr (Tnum 0))) in H2.
    rewrite H2 in H3. congruence. simpl. unfold compose,bind,pure. rewrite H5. rewrite H1. rewrite H10. reflexivity.
    eapply fromExp_IsCompiled; eauto. eapply fromContr_IsCompiled; eauto. eapply fromContr_IsCompiled; eauto.
    simpl in *. option_inv_auto. destruct_vals.
    assert (ILBVal b0 = ILBVal false). eapply specialiseExp_ILsem_sound; eauto. simpl. rewrite adv_ext_0. eassumption.
    unfold fromBLit in H. destruct (specialiseExp b env ext);tryfalse. destruct op;tryfalse. destruct args; tryfalse. some_inv.
    simpl. reflexivity. reflexivity. inversion H0. subst. erewrite t_now_before_cutPayoff_exp; eauto.
    simpl in *. option_inv_auto. destruct_vals.
    assert (ILBVal b0 = ILBVal false). eapply specialiseExp_ILsem_sound; eauto. simpl. rewrite adv_ext_0. eassumption.
    unfold fromBLit in H. destruct (specialiseExp b env ext);tryfalse. destruct op;tryfalse. destruct args; tryfalse. some_inv.
    simpl. reflexivity. reflexivity. inversion H0. subst; eauto.
  - intros. inversion HC. inversion T. subst. simpl in *. option_inv_auto. simpl in *. option_inv_auto. destruct_vals.
    destruct n0.
    + simpl in *. option_inv_auto. assert (x2 = ILBVal true).
      eapply specialiseExp_ILsem_sound; eauto. simpl. rewrite adv_ext_0. eassumption.
      unfold fromBLit in H. destruct (specialiseExp b env ext);tryfalse. destruct op;tryfalse. destruct args; tryfalse. some_inv.
      simpl. reflexivity. reflexivity. inversion H0. subst. eauto.
    + simpl in *. option_inv_auto. assert (x2 = ILBVal true).
      eapply specialiseExp_ILsem_sound; eauto. simpl. rewrite adv_ext_0. eassumption.
      unfold fromBLit in H. destruct (specialiseExp b env ext);tryfalse. destruct op;tryfalse. destruct args; tryfalse. some_inv.
      simpl. reflexivity. reflexivity. inversion H0. subst. eauto.
Qed.


(* N step contract reduction *)
Inductive RedN : nat -> Contr -> EnvP -> ExtEnvP -> Contr ->  Prop :=
    red_refl c envp extp : RedN O c envp extp c
  | red_step c c' c'' n envp extp tr : RedN n c envp extp c'' -> Red c'' envp extp c' tr ->
                             RedN (S n) c envp extp c'.

Hint Constructors RedN Red.

Example RedN_ex1 : forall envp extp cur p1 p2,
                     RedN 3 (Translate (Tnum 2) (Transfer cur p1 p2)) envp extp Zero.
Proof.
  intros. econstructor. econstructor. econstructor. econstructor. econstructor.
  reflexivity. reflexivity. econstructor.
  reflexivity. reflexivity.
  econstructor. econstructor. econstructor. reflexivity.
Qed.

Lemma adv_disc_0 d:
  adv_disc 0 d = d.
Proof.
  unfold adv_disc. simpl. apply functional_extensionality. reflexivity.
Qed.

Lemma fromContr_Red_exists c c' t0 tr extp envp il_e:
  fromContr c t0 = Some il_e ->
  Red c envp extp c' tr ->
  exists il_e', fromContr c' t0 = Some il_e'.
Proof.
Admitted.

Lemma fromContr_RedN_exists c c' n t0 extp envp il_e:
  fromContr c t0 = Some il_e ->
  RedN n c envp extp c' ->
  exists il_e', fromContr c' t0 = Some il_e'.
Proof.
  Admitted.

Lemma fromContr_ILsem_Red_exists c c' t0 tr extp envp il_e il_e' disc p1 p2 extIL tenv r:
  fromContr c t0 = Some il_e ->
  Red c envp extp c' tr ->
  fromContr c' t0 = Some il_e' ->
  IL[|il_e|]extIL tenv 0 0 disc p1 p2 = Some (ILRVal r) ->
  exists r', IL[|cutPayoff il_e'|](adv_ext 1 extIL) tenv 0 1 disc p1 p2 = Some (ILRVal r').
Proof.
  Admitted.

Lemma fromContr_ILsem_RedN_exists c c' n t0 extp envp il_e il_e' disc p1 p2 extIL tenv r:
  fromContr c t0 = Some il_e ->
  RedN n c envp extp c' ->
  fromContr c' t0 = Some il_e' ->
  IL[|cutPayoff il_e|]extIL tenv 0 (S n) disc p1 p2 = Some (ILRVal r) ->
  exists r', IL[|cutPayoff il_e'|](adv_ext (Z.of_nat n) extIL) tenv 0 1 disc p1 p2 = Some (ILRVal r').
Proof.
Admitted.

Definition cutPayoff_sound c n :=
  forall envC extC (il_e : ILExpr) (extIL : ExtEnv' ILVal) (envP : EnvP) (extP : ExtEnvP)
         (v' : ILVal) m n0 p1 p2 curr v trace (disc : nat -> R ) tenv,
  (forall a a', Asset.eqb a a' = true) ->
  (forall l t, fromVal (extC l t) = extIL l t) ->
  IsClosedCT c ->
  fromContr c (ILTexpr (Tnum n0)) = Some il_e ->
  C[|Translate (Tnum n0) c|] envC extC tenv = Some trace ->
  m + n = horizon c tenv ->
  sum_list (map (fun t => (disc t * trace t p1 p2 curr)%R)
                (seq (n+n0) m)) = v ->
  IL[|cutPayoff il_e|] extIL tenv 0 (n+n0) disc p1 p2 = Some v'->
  fromVal (RVal v) = v'.

Hint Resolve delay_empty_trace.

Lemma cutPayoff_sound_base c : cutPayoff_sound c 0.
Proof.
  unfold cutPayoff_sound. intros.
  eapply Contr_translation_sound with (tenv:=tenv) (envC:=envC) (disc:=disc); eauto;
  try rewrite plus_0_r in *; try rewrite plus_0_l in *; subst; try eassumption; try reflexivity.
  erewrite ILexpr_eq_cutPayoff_at_n with (c:=c) (t0:=(ILTexpr (Tnum n0))); try eassumption. reflexivity.
  simpl. apply not_true_is_false. intro. apply ltb_lt in H4. omega.
Qed.

Lemma cp_Scale_inversion c n e :
  cutPayoff_sound (Scale e c) n -> cutPayoff_sound c n.
Proof.
Admitted.

Lemma cp_Translate_inversion c t0 n :
  cutPayoff_sound (Translate t0 c) n -> cutPayoff_sound c n.
Proof.
Admitted.

Lemma sum_delay_n':
  forall (n n0 : nat) (tr : Trace) (p1 p2 : Party) (curr : Asset) (f : nat -> R) (t0 n1 : nat),
  sum_list (map (fun t : nat => (f t * delay_trace (n0 + n) tr t p1 p2 curr)%R) (seq (t0 + n0) n1)) =
  sum_list (map (fun t : nat => (f (n0 + t)%nat * delay_trace n tr t p1 p2 curr)%R) (seq t0 n1)).
Proof.
  Admitted.

Lemma cp_sound_translate_1 c n :
  cutPayoff_sound c n -> cutPayoff_sound (Translate (Tnum 1) c) (1 + n).
Proof.
  unfold cutPayoff_sound.
  intros until tenv; intros A Xeq TC CC Cs Hor Sm ILs.
  inversion TC.
  eapply H with (m:=m) (n0:= S n0);eauto.
  + rewrite Equivalence.transl_iter in Cs. replace (S n0) with (n0 + 1) by ring.
    apply Cs.
  + simpl in *. destruct (horizon c tenv). destruct m;simpl in *;tryfalse.
    simpl in Hor. omega.
  + simpl in *. replace (n + S n0) with (S (n + n0)) by ring. eapply Sm.
  + replace (n + S n0) with (S (n + n0)) by ring. eapply ILs.
Qed.

Fixpoint transl_one_iter (n : nat) (c : Contr) :=
  match n with
  | O => Translate (Tnum 1) c
  | S n' => Translate (Tnum 1) (transl_one_iter n' c)
  end.

(* I think, this property is required for the n-step proof *)
Lemma cp_summ c n :
  forall envC extC (il_e : ILExpr) (extIL : ExtEnv' ILVal) (envP : EnvP) (extP : ExtEnvP)
         (v' : ILVal) m n0 p1 p2 curr v v'' trace (disc : nat -> R ) tenv,
    (forall a a', Asset.eqb a a' = true) ->
    (forall l t, fromVal (extC l t) = extIL l t) ->
    IsClosedCT c ->
    fromContr c (ILTexpr (Tnum n0)) = Some il_e ->
    C[|Translate (Tnum n0) c|] envC extC tenv = Some trace ->
    m + n = horizon c tenv ->
    sum_list (map (fun t => (disc t * trace t p1 p2 curr)%R)
                  (seq (n+n0) m)) = v ->
    IL[|cutPayoff il_e|] extIL tenv 0 (n+n0) disc p1 p2 = Some v' ->
    fromVal (RVal v) = v' ->
    IL[|cutPayoff il_e|] extIL tenv 0 (1+n+n0) disc p1 p2 = Some (ILRVal v'') ->
    v' = ILRVal (trace (n+n0)%nat p1 p2 curr + v'')%R.
Proof.
  Admitted.
  
Lemma cutPayoff_sound_step c n :
      cutPayoff_sound c n -> cutPayoff_sound c (1 + n).
Proof.
  generalize dependent n.
  induction c; intros until tenv; intros A Xeq TC CC Cs Hor S ILs.
  - (* zero *)
    simpl in *. some_inv. subst. simpl in *.
    unfold compose,bind,pure in *. some_inv. rewrite sum_of_map_empty_trace; auto.
  - (* let *)
    simpl in *. option_inv_auto.
  - (* transf *)
    intros. simpl in *. option_inv_auto. unfold compose in *. some_inv.
    remember (Party.eqb p p0) as b0.
    destruct b0.
    + simpl in *. assert (Hmeq0 : m=0) by omega. subst. simpl. some_inv. reflexivity.
    + simpl in *. assert (Hmeq0 : m=0) by omega. assert (Hneq0 : n = 0 ) by omega. subst. simpl.
      rewrite plus_0_l in *.
      assert (Hlt_true : (n0 <? S n0) = true). apply ltb_lt. omega.
      rewrite Hlt_true in *. some_inv. reflexivity.
  - (* scale *)
    intros. simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
    destruct_vals. some_inv. subst. rewrite delay_trace_scale.
    unfold scale_trace, compose, scale_trans.
    rewrite summ_list_common_factor. rewrite <- fromVal_RVal_eq. apply fromVal_RVal_f_eq.
    + erewrite <- cutPayoff_eq_compiled_expr in H5; try eassumption.
      eapply Exp_translation_sound with (t0':=0) (envT:=tenv) (envC:=envC);
        try (simpl in *; some_inv; subst); try eassumption.
      rewrite Z.add_0_r. assumption.
    + inversion TC. apply cp_Scale_inversion in H.
      eapply IHc with (envC:=envC); eauto. simpl. autounfold.
      rewrite H2. reflexivity.
  - (* translate *)
    intros.
    simpl in *. option_inv_auto. rewrite delay_trace_swap.
    inversion TC. subst. simpl in *.
    rename n1 into t0.
    simpl in *.
    rewrite adv_ext_iter in H2.
    replace (Z.of_nat n0 + Z.of_nat t0)%Z with (Z.of_nat (t0 + n0)) in *.
    rewrite delay_trace_iter.
    destruct t0.
    * apply cp_Translate_inversion in H.
      rewrite add_0_r. simpl in *. rewrite <- fromVal_RVal_eq.
      eapply IHc with (envC:=envC);eauto.
      simpl. autounfold. rewrite H2. reflexivity.
      destruct (horizon c tenv);destruct m;simpl in *;tryfalse;auto.
    * apply cp_Translate_inversion in H.
      destruct t0. unfold cutPayoff_sound in H.
      ** eapply H with (m:=m) (n0:= S n0);eauto.
         *** simpl. autounfold.
             (* replace (Z.of_nat n0 + 1)%Z with (1 + Z.of_nat n0)%Z by ring. *)
             (* rewrite succ_of_nat with (t:=0%Z). simpl.          *)
             simpl in H2. rewrite H2. autounfold. reflexivity.
         *** simpl in *. destruct (horizon c tenv). destruct m;simpl in *; tryfalse.
             simpl in *. omega.
         *** simpl. replace (n0 +1) with (S n0) by ring.
             replace (n + S n0) with (S (n + n0)) by ring. reflexivity.
         *** replace (n + S n0) with (S (n + n0)) by ring. assumption.
Admitted.

Theorem cutPayoff_sound_n_steps c n: cutPayoff_sound c n.
Proof.
  induction n.
  - apply cutPayoff_sound_base.
  - apply cutPayoff_sound_step. apply IHn.
Qed.
