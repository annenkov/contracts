(* Lemmas and sketch of the proof of the n-step reduction *)
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
Require Import CutPayoff.

Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import FunctionalExtensionality.
Require Import Coq.Program.Equality.

Import Nat.

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

Definition cutPayoff_sound c n g n0 :=
  forall envC extC (il_e : ILExpr) (extIL : ExtEnv' ILVal) (envP : EnvP) (extP : ExtEnvP)
         (v' : R) m p1 p2 curr v trace (disc : nat -> R ) tenv,
  (forall a a', Asset.eqb a a' = true) ->
  (forall l t, fromVal (extC l t) = extIL l t) ->
  TypeExt extC ->
  TypeEnv g envC ->
  g |-C c ->
  IsClosedCT c ->
  fromContr c (ILTexpr (Tnum n0)) = Some il_e ->
  C[|Translate (Tnum n0) c|] envC extC tenv = Some trace ->
  n + m = horizon c tenv ->
  sum_list (map (fun t => (disc t * trace t p1 p2 curr)%R)
                (seq (n+n0) m)) = v ->
  IL[|cutPayoff il_e|] extIL tenv 0 (n+n0) disc p1 p2 = Some (ILRVal v')->
  fromVal (RVal v) = ILRVal v'.

Hint Resolve delay_empty_trace.

Lemma cutPayoff_sound_base c g t0 : cutPayoff_sound c 0 g t0.
Proof.
  unfold cutPayoff_sound. intros.
  eapply Contr_translation_sound with (tenv:=tenv) (envC:=envC) (disc:=disc); eauto;
  try rewrite plus_0_r in *; try rewrite plus_0_l in *; subst; try eassumption; try reflexivity.
  erewrite ILexpr_eq_cutPayoff_at_n with (c:=c) (t0:=(ILTexpr (Tnum t0))); try eassumption. reflexivity.
  simpl. apply not_true_is_false. intro. apply Nat.ltb_lt in H7. omega.
Qed.

Lemma cutPayoff_sound_1 c g n0 : cutPayoff_sound c 1 g n0.
Proof.
  induction c; intros until tenv; intros A Xeq TyExt TyEnv TyC Hclosed TC Cs Hor Sum ILs; inversion Hclosed; inversion TyC.
  - (* zero *)intros. inversion Hor.
  - (* let *)
    intros. simpl in *.
    option_inv_auto.
  - (* transf *)
    intros. simpl in *. option_inv_auto. unfold compose in *. some_inv.
    (*rewrite delay_trace_n_m; try omega. replace (S t0 - t0) with 1 by omega. simpl.
    unfold empty_trans. replace ((disc _) * 0 + 0)%R with 0%R by ring.*)
    destruct (Party.eqb p p0).
    + simpl in *. some_inv. assert (m = 0) by omega. subst. reflexivity.
    + simpl in *. assert (n0 <? S n0 = true). apply ltb_lt. omega.
      assert (m = 0) by omega. subst.
      rewrite H in ILs. some_inv. reflexivity.
  - (* scale *)
    intros. simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
    destruct_vals. some_inv. subst. rewrite <- delay_scale_trace. unfold scale_trace, compose, scale_trans.
    rewrite summ_list_common_factor. rewrite <- fromVal_RVal_eq. apply fromVal_RVal_f_eq.
    erewrite <- cutPayoff_eq_compiled_expr in H7; try eassumption.
    + eapply Exp_translation_sound with (t0':=0); try (simpl in *; some_inv; subst); try eassumption. simpl.
      rewrite Zplus_0_r. eassumption.
    + eapply IHc; eauto. autounfold in *. simpl.
      rewrite H1. reflexivity.
  - (* translate *)
    intros. subst. simpl in *. option_inv_auto.
    destruct n.
    + simpl in *. destruct (horizon c tenv) eqn:Hhor.
      * inversion Hor.
        (* simpl. eapply IHc; eauto. rewrite adv_ext_0 in H1. rewrite H1. reflexivity. rewrite Hhor. reflexivity. *)
      * simpl in *. eapply IHc; simpl;eauto. unfold liftM,compose,pure,bind.
        rewrite adv_ext_0 in H2. rewrite H2. reflexivity.
        inversion Hor. subst. rewrite delay_trace_0. reflexivity.
    + simpl in *.
      eapply Contr_translation_sound with (disc:=disc) (envC:=envC) (tenv:=tenv) (t0':=0);
        eauto; try reflexivity. simpl.
      unfold liftM,compose,bind,pure. erewrite adv_ext_iter in H2. rewrite Zpos_P_of_succ_nat in H2. rewrite plus_0_r.
      rewrite plus_comm. rewrite Zpos_P_of_succ_nat. rewrite Nat2Z.inj_add.
      replace (Z.succ (Z.of_nat n0 + Z.of_nat n)) with  (Z.of_nat n0 + Z.succ (Z.of_nat n))%Z by ring.
      rewrite H2. reflexivity. rewrite plus_0_r. simpl.
      rewrite delay_trace_iter. replace (S n + n0) with (n + S n0) by ring.
      destruct (horizon c tenv) eqn:Hhor.
      * inversion Hor.
      * unfold plus0. simpl in *. inversion Hor. subst.
        (* replace (S n + S n0 - 1) with (n + (S (S n0) - 1)) by omega. *)
        rewrite sum_delay. simpl.
        simpl. replace (n + S n0) with (S (n0 + n)) by ring.
           replace (S (n0 + n)) with (S (n + n0)) by ring. reflexivity.
      * erewrite <- ILexpr_eq_cutPayoff_at_n in ILs. eassumption. eauto. eauto. simpl.
        apply not_true_is_false. unfold not. intros. apply ltb_lt in H. omega.
  - (* Both *)
    admit.
  - (* If *)
    admit.
Admitted.

Lemma cp_Scale_inversion c n e il G t0:
  G |-E e ∶ REAL ->
  (fromExp (ILTexprZ (ILTexpr (Tnum t0))) e = Some il) ->
  cutPayoff_sound (Scale e c) n G t0 -> cutPayoff_sound c n G t0.
Proof.
  intros TyE He H. unfold cutPayoff_sound in H.
  intros until tenv; intros A Xeq TyExt TyEnv TyC Hclosed TC Cs Hor Sum ILs.
  assert (Hadv : TypeExt (adv_ext (Z.of_nat t0) extC) ) by (apply adv_ext_type;apply TyExt).
  assert (HH := Esem_typed_total _ _ _ _ _ TyE TyEnv Hadv).
  destruct HH as [r H']. destruct H' as [Hr Hc]. inversion Hc. subst.
  simpl in *. option_inv_auto.
  eapply H with (il_e := (ILBinExpr ILMult il il_e)) (trace:=delay_trace t0 (scale_trace b x));eauto; simpl in *; unfold liftM,liftM2,compose,pure,bind.
  - rewrite He. rewrite TC. reflexivity.
  - rewrite H1.
    rewrite Hr.
    simpl. reflexivity.
  - admit.
  - rewrite ILs. admit.
Admitted.

Lemma cp_Translate_inversion_0 c n g t0:
  cutPayoff_sound (Translate (Tnum 0) c) n g t0 -> cutPayoff_sound c n g t0.
Proof.
  intros H.
  intros until tenv; intros A Xeq TyExt TyEnv TyC Hclosed TC Cs Hor Sum ILs.
  simpl in *. option_inv_auto. unfold cutPayoff_sound in *.
  eapply H;eauto. simpl. unfold liftM,liftM2,compose,pure,bind.
  - rewrite adv_ext_iter. replace (Z.of_nat t0 + 0)%Z with (Z.of_nat t0) by omega.
    rewrite H1. rewrite delay_trace_iter. reflexivity.
  - simpl. rewrite Hor. destruct (horizon c tenv);reflexivity.
Qed.


Lemma cp_Translate_inversion c n g t0:
  cutPayoff_sound (Translate (Tnum 1) c) (1+n) g t0 -> cutPayoff_sound c n g (S t0).
Proof.
  intros H.
  intros until tenv; intros A Xeq TyExt TyEnv TyC Hclosed TC Cs Hor Sum ILs.
  simpl in *. option_inv_auto. unfold cutPayoff_sound in *.
  eapply H;eauto. simpl. unfold liftM,liftM2,compose,pure,bind.
  - rewrite adv_ext_iter.
     assert (Ht0 :(Z.pos (Pos.of_succ_nat t0)) = (Z.of_nat t0 + 1)%Z).
     {rewrite Zpos_P_of_succ_nat. omega. }
     rewrite Ht0 in *. rewrite H1. reflexivity.
  - simpl. rewrite Hor. unfold plus0. destruct (horizon c tenv);try reflexivity. admit.
  - rewrite delay_trace_iter. replace (n + S t0) with (S n + t0) by omega. reflexivity.
  - replace (S n + t0) with (n + S t0) by omega. assumption.
 Admitted.


Lemma sum_delay_n':
  forall (n n0 : nat) (tr : Trace) (p1 p2 : Party) (curr : Asset) (f : nat -> R) (t0 n1 : nat),
  sum_list (map (fun t : nat => (f t * delay_trace (n0 + n) tr t p1 p2 curr)%R) (seq (t0 + n0) n1)) =
  sum_list (map (fun t : nat => (f (n0 + t)%nat * delay_trace n tr t p1 p2 curr)%R) (seq t0 n1)).
Proof.
  Admitted.

Lemma cp_sound_translate_1 c n g t0:
  cutPayoff_sound c n g (S t0) -> cutPayoff_sound (Translate (Tnum 1) c) (1 + n) g t0.
Proof.
  unfold cutPayoff_sound.
  intros until tenv; intros A Xeq TyExt TyEnv TyC Hclosed TC Cs Hor Sum ILs.
  inversion Hclosed. inversion TyC. subst.
  eapply H with (m:=m);eauto.
  + rewrite Equivalence.transl_iter in Cs. replace (S t0) with (t0 + 1) by ring.
    apply Cs.
  + simpl in *. destruct (horizon c tenv). destruct m;simpl in *;tryfalse.
    simpl in Hor. omega.
  + simpl in *. replace (n + S t0) with (S (n + t0)) by ring. reflexivity.
  + replace (n + S t0) with (S (n + t0)) by ring. eapply ILs.
Qed.

Fixpoint transl_one_iter (n : nat) (c : Contr) :=
  match n with
  | O => Translate (Tnum 1) c
  | S n' => Translate (Tnum 1) (transl_one_iter n' c)
  end.

(* I think, this property is required for the n-step proof *)
Lemma cp_summ c n :
  forall envC extC (il_e : ILExpr) (extIL : ExtEnv' ILVal) (envP : EnvP) (extP : ExtEnvP)
         (v' : R) m n0 p1 p2 curr v v' trace (disc : nat -> R ) tenv,
    (forall a a', Asset.eqb a a' = true) ->
    (forall l t, fromVal (extC l t) = extIL l t) ->
    IsClosedCT c ->
    fromContr c (ILTexpr (Tnum n0)) = Some il_e ->
    C[|c|] envC (adv_ext (Z.of_nat n0) extC) tenv = Some trace ->
    m + n = horizon c tenv ->
    sum_list (map (fun t => (disc t * trace t p1 p2 curr)%R)
                  (seq (n+n0) m)) = v ->
    IL[|cutPayoff il_e|] extIL tenv 0 (1+n) disc p1 p2 = Some (ILRVal v') ->
    IL[|cutPayoff il_e|] extIL tenv 0 n disc p1 p2 =
    Some (ILRVal (disc n * delay_trace n0 trace n p1 p2 curr + v')%R).
Proof.
  Admitted.

Lemma ILRVal_plus v v' l: ILRVal (l + v) = ILRVal (l + v') -> ILRVal v = ILRVal v'.
Proof.
  intros H. apply f_equal. inversion H. eapply Rplus_eq_reg_l;eauto.
Qed.

Lemma cutPayoff_sound_step c n g :
      cutPayoff_sound c n g 0 -> cutPayoff_sound c (1 + n) g 0.
Proof.
  generalize dependent n.
  induction c;intros until tenv; intros A Xeq TyExt TyEnv TyC Hclosed TC Cs Hor Sum ILs; inversion Hclosed; inversion TyC.
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
      rewrite plus_0_l in *.  some_inv. reflexivity.
  - (* scale *)
    intros. simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
    destruct_vals. some_inv. subst. rewrite delay_trace_scale.
    unfold scale_trace, compose, scale_trans.
    rewrite summ_list_common_factor. rewrite <- fromVal_RVal_eq. apply fromVal_RVal_f_eq.
    + erewrite <- cutPayoff_eq_compiled_expr in H8; try eassumption.
      eapply Exp_translation_sound with (t0':=0) (envT:=tenv) (envC:=envC);
        try (simpl in *; some_inv; subst); try eassumption.
    + eapply cp_Scale_inversion in H;eauto.
      eapply IHc with (envC:=envC); eauto.
      simpl. autounfold.
      rewrite H2. reflexivity.
  - (* translate *)
    intros.
    simpl in *. option_inv_auto. rewrite delay_trace_swap.
    inversion TC. subst. simpl in *.
    simpl in *.
    rewrite adv_ext_iter in H2.
    rewrite delay_trace_iter. rewrite add_0_l in *. rewrite add_0_r in *.
    destruct n0.
    * simpl in *.
      apply cp_Translate_inversion_0 in H.
      eapply IHc with (envC:=envC);eauto.
      simpl. autounfold. rewrite H2. reflexivity. simpl in *.
      destruct (horizon c tenv);simpl in *;tryfalse. apply Hor.
      rewrite add_0_r in *. reflexivity. rewrite add_0_r in *. auto.
    * unfold cutPayoff_sound in H.
      remember (sum_list
       (map (fun t1 : nat => (disc t1 * delay_trace (S n0) x0 t1 p1 p2 curr)%R)
            (seq (S n) m))) as q.
      rewrite add_0_r in *.
      apply ILRVal_plus with (l:= (disc n * delay_trace (S n0) x0 n p1 p2 curr)%R).
      rewrite <- fromVal_RVal_eq.
      eapply H with (tenv:=tenv) (disc:=disc) (m:=1+m);eauto.
      ** simpl. rewrite add_0_r in *. eauto.
      ** simpl. unfold liftM,liftM2,compose,pure,bind.
         rewrite Zpos_P_of_succ_nat in *. rewrite <- Nat2Z.inj_succ.
         rewrite adv_ext_iter.
         replace (0 + Z.of_nat (S n0))%Z with (Z.of_nat (S n0)) in * by ring.
         rewrite H2. reflexivity.
      ** admit.
      ** rewrite delay_trace_iter. rewrite add_0_r in *.
         simpl in *. subst q. reflexivity.
      ** eapply cp_summ with (n0 :=1+n0);eauto.
         unfold plus0 in *. destruct (horizon c tenv);tryfalse;eauto. admit.
  - (* Both*)
    (* We split values on two summands an apply induction hypothes
       Here we use an inversion principle for [both] (similar to [scale]) to
       obtain the premises for IHs *)
    admit.
  - (* If-within *)
    (* We proceed by case analisys on the outcome of evaluation of the contition.
       We perform inner induction on number of iteration for if-within construct *)
Admitted.

Theorem cutPayoff_sound_n_steps c n g : cutPayoff_sound c n g 0.
Proof.
  induction n.
  - apply cutPayoff_sound_base.
  - apply cutPayoff_sound_step. apply IHn.
Qed.
