(** Lemmas and the proof of the n-step reduction *)

(** ** Overview *)

(** We generalize one-step soundness proof and show that if cutPayoff() is sound at step n,
then it is sound at step n+1 (formulation up to omitting some technical details):

[cutPayoff_sound_step : ∀ (c : Contr) (n : nat), cutPayoff_sound c n -> cutPayoff_sound c (1 + n)]

The proof of [cutPayoff_sound_step] essentially boils down to the use of the lemma [cp_summ]:
[cp_summ] to connects the output of the evaluation after [n] steps and [n+1] steps.
We prove [cp_summ] by induction on the syntax of contracts.

Having the [cutPayoff_sound_step] lemma, we can prove the general statement for any [n] :
[cutPayoff_sound_n_steps : ∀ c n, cutPayoff_sound c n]
by induction on [n]. The base case is just the soundness of compilation theorem, and for the
induction step we use [cutPayoff_sound_step].

Note, that cutPayoff_sound is formulated in more "semantic" style and avoids speaking about
n-step reduction directly. Instead, we formulate the soundness in terms of traces, and this
point of view directly corresponds to the traces produced by the reduction semantics
(see lemmas [red_sound1] and [red_sound2] in  ../Reduction.v)

We define n-step reduction relation [RedN] as an iterated one-step reduction and prove its soundness.
We use [cutPayoff_sound_n_steps] and [RedN_sound] to prove soundness of [cutPayoff()] wrt. [RedN]
 *)

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
  | red_step c c' c'' n envp extp tr :
      Red c envp extp c' tr -> RedN n c' envp (adv_ext 1 extp) c'' ->
      RedN (S n) c envp extp c''.

Hint Constructors RedN Red.

Example RedN_ex1 : forall envp extp cur p1 p2,
                     RedN 3 (Translate (Tnum 2) (Transfer cur p1 p2)) envp extp Zero.
Proof.
  intros. repeat econstructor.
Qed.

Lemma RedN_sound  c c'  env ext envp extp t1 t2 i g tenv n :
  RedN n c envp extp c' ->
  g |-C c ->
  TypeEnv g env -> TypeExt ext ->
  ext_inst extp ext ->
  env_inst envp env ->
  C[|c|]env ext tenv = Some t1 ->
  C[|c'|] env (adv_ext (Z.of_nat n) ext) tenv = Some t2
  -> t1 (n + i) = t2 i.
Proof.
  intros R E X T I J S1 S2.
  generalize dependent t1. generalize dependent t2. generalize dependent env.
  generalize dependent ext. generalize dependent g.
  induction R.
  - intros. simpl. rewrite adv_ext_0 in S2. congruence.
  - intros. simpl.
    assert (H_c'_typed : g |-C c') by (eapply Preservation.red_typed;eauto).
    assert (Htrace_c' : exists tr, C[| c'|] env (adv_ext 1 ext) tenv = Some tr)
      by (apply Csem_typed_total with (g:=g);auto).
    destruct Htrace_c'.
    erewrite Soundness.red_sound2 with (c:=c) (c':=c');eauto.
    eapply IHR with (ext:=adv_ext 1 ext);eauto.
    rewrite adv_ext_iter. rewrite succ_of_nat with (t:=0%Z). simpl in *.
    apply S2.
Qed.

(** Soundness of cutPayoff() formulated in terms of traces.
    Notice that we use a generalized formulation that works for arbitrary
    initial value [n0]. This is often necessary to get general enough induction hypothesis.

    The intuition for this definition is that at the "current time" [n] we the outcome
    of the compiled expression evaluation should be equal to the sum of values (of the trace)
    starting from the  point [n] (as opposed to 0 for the soundness of compilation).
    I.e. we consider only a part of the trace and ignore all the trasfers before the point [n].
*)
Definition cutPayoff_sound c n g n0 :=
  forall envC extC (il_e : ILExpr) (extIL : ExtEnv' ILVal) (envP : EnvP) (extP : ExtEnvP)
         (v' : R) m k p1 p2 curr v trace (disc : nat -> R ) tenv,
  (forall a a', Asset.eqb a a' = true) ->
  (forall l t, fromVal (extC l t) = extIL l t) ->
  TypeExt extC ->
  TypeEnv g envC ->
  g |-C c ->
  IsClosedCT c ->
  fromContr c (ILTexpr (Tnum n0)) = Some il_e ->
  C[|Translate (Tnum n0) c|] envC extC tenv = Some trace ->
  n + m = k + (horizon c tenv) ->
  sum_list (map (fun t => (disc t * trace t p1 p2 curr)%R)
                (seq (n+n0) m)) = v ->
  IL[|cutPayoff il_e|] extIL tenv 0 (n+n0) disc p1 p2 = Some (ILRVal v')->
  fromVal (RVal v) = ILRVal v'.

Hint Resolve delay_empty_trace.

(** Proof of the basic case when [n=0] i.e. we do not ignore any payoffs *)
Lemma cutPayoff_sound_base c g t0 : cutPayoff_sound c 0 g t0.
Proof.
  unfold cutPayoff_sound. intros.
  eapply Contr_translation_sound
    with (tenv:=tenv) (envC:=envC) (disc:=disc) (p1:=p1) (p2:=p2) (curr:=curr); eauto;
    try rewrite plus_0_r in *; try rewrite plus_0_l in *; subst; try eassumption; try reflexivity.
  (* - destruct (horizon c tenv) eqn: Hhor_c. *)
  (*   + reflexivity. *)
  (* + unfold plus0. *)
    remember (horizon c tenv) as n.
    replace (k + n) with (n + k) by ring.
    erewrite <- sum_before_after_horizon' with (m:=n);eauto. simpl.
    destruct n.
    rewrite <- Heqn. simpl. omega.
    rewrite <- Heqn. simpl. omega.
    erewrite ILexpr_eq_cutPayoff_at_n with (c:=c) (t0:=(ILTexpr (Tnum t0)));
      try eassumption. reflexivity.
    simpl. apply not_true_is_false. intro. apply Nat.ltb_lt in H7. omega.
Qed.

Lemma ILRVal_plus v v' l : ILRVal (l + v) = ILRVal (l + v') -> ILRVal v = ILRVal v'.
Proof.
  intros H. apply f_equal. inversion H. eapply Rplus_eq_reg_l;eauto.
Qed.

Lemma ILRVal_mult v v' l :
  (l = 0%R -> False) ->
  ILRVal (l * v)%R = ILRVal (l * v')%R -> ILRVal v = ILRVal v'.
Proof.
  intros Hneq H. apply f_equal. inversion H. eapply Rmult_eq_reg_l;eauto.
Qed.


Lemma singleton_trans_self p a n : singleton_trans p p a n = empty_trans.
Proof. cbv. rewrite Party.eqb_refl. reflexivity. Qed.

Lemma singleton_trace_empty_trans : singleton_trace empty_trans = empty_trace.
Proof.
  apply functional_extensionality. intros n.
  destruct n; reflexivity.
Qed.

Tactic Notation "omegab" := try rewrite eqb_neq in *;
                        try rewrite eqb_eq in *;
                        try rewrite ltb_lt in *;
                        try rewrite leb_le in *;
                        try rewrite ltb_ge in *;
                        omega.

Lemma delay_singleton_trace_neq t n trans :
  eqb n t = false -> (delay_trace n (singleton_trace trans)) t = empty_trans.
Proof.
  intros. unfold delay_trace.
  destruct (n <=? t) eqn:Hn;auto.
  unfold singleton_trace. assert (H0 : t-n > 0) by omegab.
  destruct (t-n). inversion H0. reflexivity.
Qed.

Lemma add_trace_at tr1 tr2 t p1 p2 a :
  (add_trace tr1 tr2) t p1 p2 a = (tr1 t p1 p2 a + tr2 t p1 p2 a)%R.
Proof.
  reflexivity.
Qed.

Lemma scale_trace_at t tr k p1 p2 a :
  (scale_trace k tr) t p1 p2 a = (tr t p1 p2 a * k)%R.
Proof. reflexivity. Qed.

(** Since payoff expressions, originated from for the contract expression sublanguage
    do not depend on [t_now] parameter, it can be arbitrary *)
Lemma expr_tnow_irrel e e_il n0 t0 extIL tenv t_now1 t_now2 disc p1 p2 :
  fromExp t0 e = Some e_il ->
  IL[| e_il|] extIL tenv n0 t_now1 disc p1 p2 =
  IL[| e_il|] extIL tenv n0 t_now2 disc p1 p2.
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
                  eapply all_to_forall3 in H; inversion_clear H as [IHe1 IHe'];
                    inversion_clear IHe' as [IHe2 IHe3];
    option_inv_auto; subst; simpl in *; try some_inv; subst.
    simpl in *. unfold bind,compose.
    erewrite <- IHe1;eauto.
    erewrite <- IHe2;eauto. erewrite <- IHe3;eauto.
  - simpl in *. some_inv. reflexivity.
Qed.

(** The important observation for proving the [cutPayoff_sound_step] lemma:

    [IL[|cutPayoff il_e|] n = disc(n) * trace(n) + [IL[|cutPayoff il_e|] (1+n)]

    That is, cutting the payoffs before [n] is exactly a discounted value
    of a contract trace at the point [n] plus the value we get by
    cutting payoffs before [n+1]. Intuitively, [disc(n) * trace(n)] is
    the value that we throw away when we move "current time" from [n]
    to [n+1]

    As usual in the statement of the lemma we generalize expressions
    to work for any "initial time" [n0]. For that reason we also have to add
    [delay_trace (n0+t0)] and [(adv_ext (Z.of_nat (n0+t0)) extC)] in appropriate places.
    This is a usual approach when proving lemmas about functions with the accumulator. *)
Lemma cp_summ c n t0:
  forall envC extC (il_e : ILExpr) (extIL : ExtEnv' ILVal) (envP : EnvP) (extP : ExtEnvP)
         (v' : R) n0 p1 p2 curr v' trace (disc : nat -> R ) tenv,
    (forall a a', Asset.eqb a a' = true) ->
    (forall l t, fromVal (extC l t) = extIL l t) ->
    IsClosedCT c ->
    fromContr c (ILTexpr (Tnum n0)) = Some il_e ->
    C[|c|] envC (adv_ext (Z.of_nat (n0+t0)) extC) tenv = Some trace ->
    IL[|cutPayoff il_e|] extIL tenv t0 (1+n) disc p1 p2 = Some (ILRVal v') ->
    IL[|cutPayoff il_e|] extIL tenv t0 n disc p1 p2 =
    Some (ILRVal (disc n * delay_trace (n0+t0) trace n p1 p2 curr + v')%R).
Proof.
  revert n. revert t0. induction c;intros until tenv; intros A Xeq Hclosed TC Cs ILs;tryfalse.
  - (* Zero *)
    simpl in *. some_inv. subst. simpl in *. some_inv.
    rewrite delay_empty_trace. rewrite Rplus_0_r. cbv. replace (_ * 0)%R with 0%R by ring.
    reflexivity.
  - (* Transfer *)
    simpl in *. some_inv. subst.
    destruct (Party.eqb p p0) eqn:Heq.
    * assert (p = p0).
      { apply Party.eqb_eq;auto. }
      simpl in *. some_inv. subst. rewrite singleton_trans_self.
      rewrite singleton_trace_empty_trans. rewrite delay_empty_trace.
      replace (empty_trace n p1 p2 curr) with 0%R by reflexivity.
      replace (disc n * 0 + 0)%R with 0%R by ring. reflexivity.
    * simpl in *. destruct (t0+n0 <? S n) eqn:Hnle.
      ** some_inv. subst. rewrite Rplus_0_r.
         destruct (t0+n0 <? n) eqn:Hn0le.
         *** rewrite delay_singleton_trace_neq. cbv. repeat apply f_equal.
             ring_simplify. reflexivity. omegab.
         *** simpl. assert (t0+n0 = n) by omegab.
             replace (n0+t0) with (t0+n0) by ring. rewrite H.
             rewrite delay_trace_at. cbv. rewrite Heq.
             destruct (Party.eqb p p1); destruct (Party.eqb p0 p2);
               destruct (Party.eqb p0 p1); destruct (Party.eqb p p2);
                 try rewrite A; try (repeat f_equal; ring).
      ** some_inv.
         assert (H : ~ t0+n0 < n) by omegab. rewrite <- ltb_nlt in *. rewrite H.
         rewrite delay_singleton_trace_neq; try omegab.
         unfold empty_trans. replace (_ * 0)%R with 0%R by ring. rewrite Rplus_0_l.
         congruence.
  - (* Scale *)
    simpl in *. option_inv_auto. inversion Hclosed. subst. some_inv.
    simpl in *. subst. simpl in *. option_inv_auto. unfold bind,compose.
    destruct x4,x5; tryfalse. some_inv. subst.
    assert (HIL1 : IL[| cutPayoff x2|] extIL tenv t0 n disc p1 p2 =
                   Some (ILRVal r)).
    {erewrite <- cutPayoff_eq_compiled_expr;eauto.
     erewrite <- cutPayoff_eq_compiled_expr in H6;eauto.
     erewrite expr_tnow_irrel;eauto. }
    assert (HIL2 : IL[| cutPayoff x3|] extIL tenv t0 n disc p1 p2 =
                   Some (ILRVal (disc n * delay_trace (n0+t0) x0 n p1 p2 curr + r0))).
    { eapply IHc;eauto. }
    rewrite HIL1. rewrite HIL2.
    destruct x1;tryfalse. simpl in *.  some_inv. subst.
    assert (Hr : fromVal (RVal x) = (ILRVal r)).
    { eapply Exp_translation_sound with (e:=e) (il_e := x2) (t0':=t0);eauto.
      simpl. rewrite <- Nat2Z.inj_add. eauto.
      erewrite <- cutPayoff_eq_compiled_expr in H6;eauto. }
    inversion Hr.
    repeat apply f_equal.
    rewrite delay_trace_scale. rewrite scale_trace_at.
    ring.
  - (* Translate *)
    simpl in *. option_inv_auto. inversion Hclosed. subst. simpl in *.
    rewrite delay_trace_iter. rewrite adv_ext_iter in H0. repeat rewrite <- Nat2Z.inj_add in H0.
    replace (n0 + t1 + n1) with (n1 + n0 + t1) in H0  by ring.
    replace (n1 + (n0 + t1)) with (n1+n0+t1) by ring.
    eapply IHc with (n0:=n1+n0) (t0:=t1);eauto.
  - (* Both *)
    simpl in *. option_inv_auto. inversion Hclosed. subst.
    some_inv. subst. simpl in *. option_inv_auto. unfold bind,compose.
    destruct x3,x4; tryfalse.
    assert (HIL1 : IL[| cutPayoff x1|] extIL tenv t0 n disc p1 p2 =
                   Some (ILRVal (disc n * delay_trace (n0+t0) x n p1 p2 curr + r))).
    { eapply IHc1;eauto.  }

    assert (HIL2 : IL[| cutPayoff x2|] extIL tenv t0 n disc p1 p2 =
                   Some (ILRVal (disc n * delay_trace (n0+t0) x0 n p1 p2 curr + r0))).
    { eapply IHc2;eauto. }
    rewrite HIL1. rewrite HIL2.
    f_equal. f_equal. rewrite delay_trace_add. rewrite add_trace_at.
    some_inv. subst. ring.
  - (* If(e,n1,c1,c2) *)
    simpl in *. option_inv_auto. inversion Hclosed. subst. simpl in *.
    clear Hclosed.
    generalize dependent n. generalize dependent t1.
    generalize dependent trace.
    (* We start with induction on [n1], this allows to simplify the
       [within_sem] and do case analisys on the outcome of the evaluation of [e] *)
    induction n1 as [|m];intros.
    * (* n1 = 0 *)
      simpl in *.
      option_inv_auto.
      remember (E[| e|] envC (adv_ext (Z.of_nat (n0 +t1)) extC)) as cond.
      remember (IL[| x1|] extIL tenv t1 (S n) disc p1 p2) as cond_il.
      unfold bind,compose.
      destruct cond;tryfalse.
      destruct v;tryfalse.
      destruct cond_il;tryfalse.
      destruct x2;tryfalse. some_inv. subst.
      (* case analysis on the outcome of the conditional expression evaluation *)
      destruct b.
      ** (* true *)
         assert (fromVal (BVal true) = ILBVal b0).
         { eapply Exp_translation_sound with (t0':=t1);simpl;eauto.
           simpl. rewrite <- Nat2Z.inj_add.
          symmetry. eauto. }
         erewrite expr_tnow_irrel with (t_now2:=1+n);eauto.
         simpl. rewrite <- Heqcond_il.
         inversion H. subst.
         eapply IHc1;eauto.
      ** (* false *)
        assert (fromVal (BVal false) = ILBVal b0).
         { eapply Exp_translation_sound with (t0':=t1);simpl;eauto.
           simpl. rewrite <- Nat2Z.inj_add.
           symmetry. eauto. }
         erewrite expr_tnow_irrel with (t_now2:=1+n);eauto.
         simpl. rewrite <- Heqcond_il.
         inversion H. subst.
         eapply IHc2;eauto.
    * (* n1 = S m *)
      simpl in *.
      option_inv_auto.
      remember (E[| e|] envC (adv_ext (Z.of_nat (n0+t1)) extC)) as cond.
      remember (IL[| x1|] extIL tenv t1 (S n) disc p1 p2) as cond_il.
      unfold bind,compose.
      destruct cond;tryfalse.
      destruct v;tryfalse.
      destruct cond_il;tryfalse.
      destruct x2;tryfalse. some_inv. subst.
      (* case analysis on the outcome of the conditional expression evaluation *)
      destruct b.
      ** (* true *)
         assert (fromVal (BVal true) = ILBVal b0).
         { eapply Exp_translation_sound with (t0':=t1);simpl;eauto.
           simpl. rewrite <- Nat2Z.inj_add.
           symmetry. eauto. }
         erewrite expr_tnow_irrel with (t_now2:=1+n);eauto.
         simpl. rewrite <- Heqcond_il.
         inversion H. subst.
         eapply IHc1;eauto.
      ** (* false *)
        option_inv_auto.
        assert (fromVal (BVal false) = ILBVal b0).
         { eapply Exp_translation_sound with (t0':=t1);simpl;eauto.
           simpl. rewrite <- Nat2Z.inj_add.
           symmetry. eauto. }
         erewrite expr_tnow_irrel with (t_now2:=1+n);eauto.
         simpl. rewrite <- Heqcond_il.
         inversion H. subst.
         erewrite IHm with (trace:=x2);eauto. rewrite delay_trace_iter.
         replace (1 + (n0 + t1)) with (n0 + S t1) by ring.
         reflexivity.
         rewrite adv_ext_iter in H3.
         replace (S t1) with (1 + t1) by ring.
         repeat rewrite Nat2Z.inj_add in *.
         replace (Z.of_nat n0 + (Z.of_nat 1 + Z.of_nat t1))%Z  with
             (Z.of_nat n0 + Z.of_nat t1 + 1)%Z by ring.
         assumption.
Qed.

Lemma cutPayoff_sound_step c n g :
  cutPayoff_sound c n g 0 -> cutPayoff_sound c (1 + n) g 0.
Proof.
  intros H.
  intros until tenv; intros A Xeq TyExt TyEnv TyC Hclosed TC Cs Hor Sum ILs.
  apply ILRVal_plus with (l:= (disc n * delay_trace 0 trace n p1 p2 curr)%R).
  eapply H with (p1:=p1) (p2:=p2) (curr:=curr) (disc:=disc) (m:=1+m);eauto.
  rewrite <- Hor. omega.
  simpl. subst. repeat rewrite add_0_r. rewrite delay_trace_0.
  reflexivity.
  erewrite cp_summ;eauto. rewrite add_0_r. reflexivity.
  simpl in *. option_inv_auto. rewrite delay_trace_0.
  eapply H1;auto.
Qed.


Theorem cutPayoff_sound_n_steps c n g :
  cutPayoff_sound c n g 0.
Proof.
  induction n.
  - apply cutPayoff_sound_base.
  - apply cutPayoff_sound_step; apply IHn;auto.
Qed.

Theorem cutPayoff_sound_RedN c c' (envC := nil) extC :
  forall (il_e : ILExpr) (extIL : ExtEnv' ILVal) (envP : EnvP) (extP : ExtEnvP)
         v' p1 p2 curr v trace (disc : nat -> R ) tenv (g := nil) n,
  (forall a a', Asset.eqb a a' = true) ->
  (forall l t, fromVal (extC l t) = extIL l t) ->
  fromContr c (ILTexpr (Tnum 0)) = Some il_e ->
  IsClosedCT c ->
  RedN n c envP extP c' ->
  C[|c'|] envC (adv_ext (Z.of_nat n) extC) tenv = Some trace ->
  horizon c' tenv <= horizon c tenv ->
  sum_list (map (fun t => (disc (n+t)%nat * trace t p1 p2 curr)%R)
                (seq 0 (horizon c' tenv))) = v ->
  IL[|cutPayoff il_e|] extIL tenv 0 n disc p1 p2 = Some (ILRVal v') ->
  TypeExt extC ->
  TypeEnv g envC ->
  g |-C c ->
  ext_inst extP extC ->
  env_inst envP envC ->
  fromVal (RVal v) = (ILRVal v').
Proof.
  simpl.
  intros until n; intros A Xeq TC R Cs S1 ILs Tx Te T J I TyExt EnvInst.
  assert (Hc_exists : exists trace0, C[|c|] envC extC tenv = Some trace0).
  { apply Csem_typed_total with (g:=nil);auto. }
  destruct Hc_exists as [trace0 Hc].
  assert (Hf : (fun t0 : nat => (disc (n+t0)%nat * trace t0 p1 p2 curr)%R) =
                 (fun t0 : nat => (disc (n+t0)%nat * trace0 (n+t0)%nat p1 p2 curr)%R)).
    { apply functional_extensionality.
      intros i.
      erewrite <- RedN_sound with (n:=n)(c:=c) (c':=c') (t2:=trace)
                                  (extp:=extP)(ext:=extC);eauto. }
    simpl in *.
    eapply cutPayoff_sound_n_steps with (n:=n) (g:=nil) (c:=c)
                                        (m:=horizon c tenv) (k:=n);simpl;eauto.
    simpl. unfold liftM,bind,compose. rewrite adv_ext_0. rewrite Hc.
    apply f_equal. rewrite delay_trace_0. reflexivity.
    rewrite <- sum_delay_plus'.
    erewrite <- Hf.
    assert (Hk : exists k, horizon c tenv = k + horizon c' tenv /\ 0 <= k) by
        (apply Nat.le_exists_sub;omega).
    destruct Hk as [k Hk']. destruct Hk' as [Hhor_eq ?].
    rewrite Hhor_eq.
    replace (k + horizon c' tenv) with (horizon c' tenv + k) by ring.
    erewrite <- sum_before_after_horizon';eauto; try omega.
    replace (n+0) with n by ring.
    assumption.
Qed.

Theorem diagram_commutes_N c c' (envC :=nil) extC:
  forall (il_e il_e' : ILExpr) (extIL : ExtEnv' ILVal) (envP : EnvP) (extP : ExtEnvP)
         p1 p2 (disc : nat -> R ) tenv (g :=nil) r r' n (a : Asset),
    (forall a a' : Asset, Asset.eqb a a' = true) ->
    (forall l t, fromVal (extC l t) = extIL l t) ->
    IsClosedCT c ->
    fromContr c (ILTexpr (Tnum 0)) = Some il_e ->
    TypeExt extC ->
    TypeEnv g envC ->
    g |-C c ->
    g |-C c' ->
    horizon c' tenv <= horizon c tenv ->
    IsClosedCT c' ->
    ext_inst extP extC ->
    env_inst envP envC ->
    RedN n c envP extP c' ->
    fromContr c' (ILTexpr (Tnum 0)) = Some il_e' ->
    IL[|cutPayoff il_e|] extIL tenv 0 n disc p1 p2 = Some (ILRVal r) ->
    IL[|il_e'|] (adv_ext (Z.of_nat n) extIL) tenv 0 0 (adv_disc n disc) p1 p2 = Some (ILRVal r') ->
    fromVal (RVal r) = ILRVal r'.
Proof.
  simpl.
  intros.
  assert (Hc_exists : exists trace, C[|c|] envC extC tenv = Some trace).
  { apply Csem_typed_total with (g:=nil);auto. }
    assert (Hc'_exists : exists trace', C[|c'|] envC (adv_ext (Z.of_nat n) extC) tenv = Some trace').
  { apply Csem_typed_total with (g:=nil);auto. }
  destruct Hc_exists as [tr Hc]. destruct Hc'_exists as [tr' Hc'].
  assert (Hpath1 :
            ILRVal (sum_list (map (fun t => (disc t * tr t p1 p2 a)%R) (seq n (horizon c tenv))))
            = ILRVal r).
  { eapply cutPayoff_sound_n_steps with (n:=n) (c:=c);eauto;replace (n+0) with n by ring.
    simpl. unfold liftM,compose,bind. rewrite adv_ext_0. rewrite Hc;reflexivity.
    rewrite delay_trace_0. reflexivity.
    assumption. }
  assert (Hpath2 :
            ILRVal (sum_list (map (fun t => (disc (n+t)%nat * tr' t p1 p2 a)%R) (seq 0 (horizon c' tenv))))
            = ILRVal r').
  { eapply Contr_translation_sound
      with (t0':=0)
           (extC:=(adv_ext (Z.of_nat n) extC))
           (disc:=(adv_disc n disc));eauto.
    - eauto.
    - simpl. unfold liftM,compose,bind. rewrite adv_ext_0.
      rewrite Hc'. rewrite delay_trace_0. reflexivity. }
    replace (n) with (n+0) in Hpath1  by ring.
    assert (Hf : (fun t0 : nat => (disc (n+t0)%nat * tr' t0 p1 p2 a)%R) =
               (fun t0 : nat => (disc (n+t0)%nat * tr (n+t0)%nat p1 p2 a)%R)).
    { apply functional_extensionality.
      intros i.
      erewrite RedN_sound with (n:=n)(c:=c) (c':=c')
                                  (extp:=extP)(ext:=extC);eauto. }
    erewrite <- sum_delay_plus' in Hpath1.
    rewrite  <- Hf in Hpath1.
    assert (Hk : exists k, horizon c tenv = k + horizon c' tenv /\ 0 <= k) by
        (apply Nat.le_exists_sub;omega).
    destruct Hk as [k Hk']. destruct Hk' as [Hhor_eq ?].
    rewrite Hhor_eq in Hpath1.
    replace (k + horizon c' tenv) with (horizon c' tenv + k) in Hpath1 by ring.
    erewrite <- sum_before_after_horizon' in Hpath1;eauto; try omega.
    congruence.
Qed.