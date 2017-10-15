(* Proofs and definitions related to contract with template variables*)
Require Import Syntax.
Require Import Denotational.
Require Import Tactics.

(* Predicate on contract template that holds only if contract does not contain template variables  *)
Inductive IsClosedCT : Contr -> Prop :=
| c_closed_zero : IsClosedCT Zero
| c_closed_let c : forall e, IsClosedCT c -> IsClosedCT (Let e c)
| c_closed_transfer cur p1 p2 : IsClosedCT (Transfer cur p1 p2)
| c_closed_scale e c : IsClosedCT c -> IsClosedCT (Scale e c)
| c_closed_translate n c : IsClosedCT c -> IsClosedCT (Translate (Tnum n) c)
| c_closed_both c1 c2 : IsClosedCT c1 -> IsClosedCT c2 -> IsClosedCT (Both c1 c2)
| c_closed_if n e c1 c2: IsClosedCT c1 -> IsClosedCT c2  -> IsClosedCT (If e (Tnum n) c1 c2).

(* Instantiate template variables according to tenv *)
Fixpoint inst_contr c tenv :=
  match c with
    | Zero => Zero
    | Let e c' => Let e (inst_contr c' tenv)
    | Transfer p1 p2 a => Transfer p1 p2 a
    | Scale e c' => Scale e (inst_contr c' tenv)
    | Translate texp c' => Translate (Tnum (TexprSem texp tenv)) (inst_contr c' tenv)
    | Both c' c'' => Both (inst_contr c' tenv) (inst_contr c'' tenv)
    | If e texp c' c'' => If e (Tnum (TexprSem texp tenv)) (inst_contr c' tenv) (inst_contr c'' tenv)
  end.

Hint Constructors IsClosedCT.

Lemma inst_contr_IsClosedCT c tenv :
  IsClosedCT (inst_contr c tenv).
Proof.
  induction c; simpl; auto.
Qed.

Lemma inst_cont_sound c tenv tenv' ext env tr tr':
  C[|c|]env ext tenv = Some tr ->
  C[|inst_contr c tenv|]env ext tenv' = Some tr' ->
  tr = tr'.
Proof.
  revert ext env tr tr'.
  induction c;intros ext env tr tr' H1 H2.
  + simpl in *. inversion H1. inversion H2. auto.
  + simpl in *. option_inv_auto.
    assert (x = x0) by congruence. subst.
    eapply IHc; eauto.
  + simpl in *. inversion H1. inversion H2. auto.
  + simpl in *. option_inv_auto.
    assert (x = x1) by congruence.
    assert (x3 = x4) by congruence. subst.
    f_equal. eauto.
  + simpl in *. option_inv_auto. f_equal. eapply IHc;eauto.
  + simpl in *. option_inv_auto. f_equal; eauto.
  + simpl in *.
    generalize dependent tr. generalize dependent tr'.
    generalize dependent ext.
    induction (TexprSem t tenv);intros.
    - simpl in *.
      destruct (E[| e|] env ext);tryfalse. destruct v;tryfalse.
      destruct b;eauto.
    - simpl in *.
      destruct (E[| e|] env ext);tryfalse. destruct v;tryfalse.
      destruct b;eauto.
      option_inv_auto.
      f_equal. eapply IHn; eauto.
Qed.

Hint Unfold bind compose pure liftM liftM2.

Lemma inst_cont_sound' c tenv tenv' ext env:
  C[|c|]env ext tenv = C[|inst_contr c tenv|]env ext tenv'.
Proof.
  revert ext env.
  induction c;intros ext env.
  + simpl in *. reflexivity.
  + simpl in *. autounfold. remember (E[| e|] env ext) as v.
    destruct v;auto.
  + simpl in *. reflexivity.
  + simpl in *. autounfold.
    remember (E[| e|] env ext) as v.
    destruct v;auto. destruct (toReal v);auto.
    rewrite IHc. reflexivity.
  + simpl in *. autounfold. rewrite IHc;reflexivity.
  + simpl in *. autounfold. rewrite IHc1. rewrite IHc2. reflexivity.
  + simpl in *.
    generalize dependent ext.
    induction (TexprSem t tenv);intros.
    - simpl in *.
      destruct (E[| e|] env ext);auto. destruct v;auto.
      destruct b;eauto.
    - simpl in *.
      destruct (E[| e|] env ext);auto. destruct v;auto.
      destruct b;auto.
      autounfold. rewrite IHn. auto.
Qed.
