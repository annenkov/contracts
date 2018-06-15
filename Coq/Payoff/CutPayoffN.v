(** Lemmas and sketch of the proof of the n-step reduction *)

(** ** Overview *)

(** We generalize one-step soundness proof and show by induction on
the structure of contracts that if cutPayoff() is sound at step n,
then it is sound at step n+1 (formulation up to omitting some
technical details):
[cutPayoff_sound_step : ∀ (c : Contr) (n : nat), cutPayoff_sound c n -> cutPayoff_sound c (1 + n)]
 The proof is by structural induction on [c] using the "inversion" lemmas
(e.g. [cp_Scale_inversion : ∀ e c n, cutPayoff_sound (Scale e c) n -> cutPayoff_sound c n])
allowing to get required premisses for the induction hypotheses.
We pay special attention to the case of [Tranlate] constructor: we use [cp_summ] to connect the
output of the evaluation after [n] steps and [n+1] steps.

Then, we can prove the general statement for any [n] :
[cutPayoff_sound_n_steps : ∀ c n, cutPayoff_sound c n]
by induction on [n] where base case is just soundness of compilation, and for the
induction step we use cutPayoff_sound_step.

 Note, that cutPayoff_sound is formulated in more "semantic" style and avoids speaking about
 n-step reduction directly. Instead we formulate the soundness in terms of traces, and this
 point of view directly corresponds to the traces produced by the reduction semantics
 (see lemmas [red_sound1] and [red_sound1] in  ../Reduction.v)*)

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

(** Soundness of cutPayoff() fomlulated in terms of traces.
    Notice that we use generalized formulation that works for arbitrary
    initial value [n0]. *)
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

(** Proof of the basic case when [n=0] i.e. we do not ignore any payoffs *)
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


(** ** Inversion lemmas *)
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

(** The important observation for proving the [Translate] case in the
    n-step soundness theorem is that

    [IL[|cutPayoff il_e|] n = disc(n) * trace(n) + [IL[|cutPayoff
    il_e|] (1+n)]

    That is, cutting payoffs before [n] is exactly a discounted value
    of a contract trace at the point [n] plus the value we get by
    cutting payoffs before [n+1]. Intuitively, [disc(n) * trace(n)] is
    the value that we throw away when we move "current time" from [n]
    to [n+1]

    As usual in the statement of the lemma we generalize expressions
    to work for any "initial time" [n0]. This is a usual approach when
    proving lemmas about function with the accumulator. *)
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


(** To simplify the development without limiting the generality, we limit ourselves to the contracts
    where [Tranlate] is defined only for a constant [1], i.e. it is of the form [Translate (Tnum 1)].
    Notice, that we do not consider template variables, since contract reduction in our setting is
    only possible after instantiating all the template variables. *)
Inductive Contr_unit_translate : Contr -> Set :=
| contr_ut_zero : Contr_unit_translate Zero
| contr_ut_let c : forall e, Contr_unit_translate c -> Contr_unit_translate (Let e c)
| contr_ut_transfer cur p1 p2 : Contr_unit_translate (Transfer cur p1 p2)
| contr_ut_scale e c : Contr_unit_translate c -> Contr_unit_translate (Scale e c)
| contr_ut_translate c : Contr_unit_translate c -> Contr_unit_translate (Translate (Tnum 1) c)
| contr_ut_both c1 c2 : Contr_unit_translate c1 -> Contr_unit_translate c2 -> Contr_unit_translate (Both c1 c2)
| contr_ut_if n e c1 c2: Contr_unit_translate c1 -> Contr_unit_translate c2 -> Contr_unit_translate (If e (Tnum n) c1 c2).

(** We define this as a "syntactic sugar" replacement for [Translate (Tnum n)] *)
Fixpoint transl_one_iter (n : nat) (c : Contr) :=
  match n with
  | O => Translate (Tnum 1) c
  | S n' => Translate (Tnum 1) (transl_one_iter n' c)
  end.

Example contr_ut_1 : Contr_unit_translate (transl_one_iter 5 Zero).
Proof. repeat constructor. Qed.

Lemma cutPayoff_sound_step c n g :
  Contr_unit_translate c ->
  cutPayoff_sound c n g 0 -> cutPayoff_sound c (1 + n) g 0.
Proof.
  generalize dependent n.  generalize dependent g.
  induction c;intros G n Hctr_ut H; intros until tenv; intros A Xeq TyExt TyEnv TyC Hclosed TC Cs Hor Sum ILs; inversion Hclosed; inversion TyC; inversion Hctr_ut;subst.
  - (* Zero *)
    simpl in *. some_inv. subst. simpl in *.
    unfold compose,bind,pure in *. some_inv. rewrite sum_of_map_empty_trace; auto.
  - (* Let *)
    simpl in *. option_inv_auto.
  - (* Transfer *)
    intros. simpl in *. option_inv_auto. unfold compose in *. some_inv.
    remember (Party.eqb p p0) as b0.
    destruct b0.
    + simpl in *. assert (Hmeq0 : m=0) by omega. subst. simpl. some_inv. reflexivity.
    + simpl in *. assert (Hmeq0 : m=0) by omega. assert (Hneq0 : n = 0 ) by omega. subst. simpl.
      rewrite plus_0_l in *.  some_inv. reflexivity.
  - (* Scale *)
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
      rewrite H3. reflexivity.
  - (* Translate *)
    intros. inversion H7. subst. simpl in *.
    simpl in *. option_inv_auto. rewrite delay_trace_swap.
      unfold cutPayoff_sound in H.
      remember (sum_list
       (map (fun t1 : nat => (disc t1 * delay_trace 1 x0 t1 p1 p2 curr)%R)
            (seq (S n) m))) as q.
      rewrite add_0_r in *. rewrite delay_trace_iter. simpl.
      apply ILRVal_plus with (l:= (disc n * delay_trace 1 x0 n p1 p2 curr)%R).
      eapply H with (tenv:=tenv) (disc:=disc) (m:=1+m);eauto.
      (* ** simpl. rewrite add_0_r in *. eauto. *)
      ** simpl. unfold liftM,liftM2,compose,pure,bind.
         rewrite H3. reflexivity.
      ** simpl. destruct (horizon c tenv);tryfalse. omega.
      ** rewrite delay_trace_iter. rewrite add_0_r in *.
         simpl in *. subst q. reflexivity.
      ** eapply cp_summ with (n0 :=1) (m:=m);eauto.
         unfold plus0 in *. destruct (horizon c tenv);tryfalse;eauto.
         omega.
  - (* Both*)
    (* We split values on two summands an apply induction hypothes
       Here we use an inversion principle for [both] (similar to [scale]) to
       obtain the premises for IHs *)
    admit.
  - (* If (-within) *)
    (* We proceed by case analisys on the outcome of the contition evaluation.
       We perform an inner induction on number of iteration for if-within construct *)
    admit.
Admitted.

Theorem cutPayoff_sound_n_steps c n g :
  Contr_unit_translate c -> cutPayoff_sound c n g 0.
Proof.
  induction n;intros H.
  - apply cutPayoff_sound_base.
  - apply cutPayoff_sound_step.
    * apply H.
    * apply IHn;auto.
Qed.
