(* Some (unfinished) attempts to generalize proof about cutPayoff
   to n step contract reduction *)
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
  simpl. apply not_true_is_false. intro. apply Nat.ltb_lt in H4. omega.
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
      assert (Hlt_true : (n0 <? S n0) = true). apply Nat.ltb_lt. omega.
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
