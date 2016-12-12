Require Import Denotational FunctionalExtensionality Bool Tactics.

(** Dual contract can be obtained from the original one by reversing
    cashflows between parties *)

Fixpoint dual (c : Contr) : Contr :=
  match c with
    | Zero => Zero
    | Let e c' => Let e (dual c')
    | Transfer p1 p2 a => Transfer p2 p1 a
    | Scale e c' => Scale e (dual c')
    | Translate v c' => Translate v (dual c')
    | Both c1 c2 => Both (dual c1) (dual c2)
    | If e d c1 c2 => If e d (dual c1) (dual c2)
  end.

Lemma party_eqb_sym x y b : Party.eqb x y = b <-> Party.eqb y x = b.
Proof.
  destruct b.
  - split; intros; apply Party.eqb_eq; apply Party.eqb_eq in H; auto.
  - split; intros; apply not_true_is_false; unfold not; intros; apply Party.eqb_eq in H0; subst;
    rewrite Party.eqb_refl in H; inversion H.
Qed.
                                                                
Hint Unfold add_trace empty_trace add_trans empty_trace const_trace empty_trans toReal.

Lemma singleton_trace_inv p1 p1' p2 p2' a a':
  (singleton_trans p1 p2 a 1 p1' p2' a' + singleton_trans p2 p1 a 1 p1' p2' a')%R = 0%R.
Proof.
  unfold singleton_trans.
    remember (Party.eqb p1 p2) as E0.
    destruct E0.
    + symmetry in HeqE0. assert (Party.eqb p2 p1 = true) by (apply party_eqb_sym; assumption). rewrite H. ring.
    + symmetry in HeqE0. assert (Party.eqb p2 p1 = false) by (apply party_eqb_sym; assumption). rewrite H.
      remember (Party.eqb p1 p2' && Party.eqb p2 p1' && Asset.eqb a a') as E1.
      destruct E1.
      * symmetry in HeqE1.
      repeat rewrite Bool.andb_true_iff in *. repeat rewrite Party.eqb_eq in *.  rewrite Asset.eqb_eq in *.
      decompose [and] HeqE1. remember (Party.eqb p1 p1' && Party.eqb p2 p2' && Asset.eqb a a') as E2.
      destruct E2.
       - symmetry in HeqE2. repeat rewrite Bool.andb_true_iff in *. repeat rewrite Party.eqb_eq in *.
        rewrite Asset.eqb_eq in *. decompose [and] HeqE2.  assert (p1 = p2) by (subst; auto).
        rewrite <- Party.eqb_eq in H5. tryfalse.
       - subst. rewrite H. rewrite HeqE0. simpl. repeat rewrite Party.eqb_refl. rewrite Asset.eqb_refl. simpl. ring.
      * symmetry in HeqE1.        
        remember (Party.eqb p1 p1' && Party.eqb p2 p2' && Asset.eqb a a') as E2.
        destruct E2.
       - symmetry in HeqE2. subst. repeat rewrite Bool.andb_true_iff in *. decompose [and] HeqE2.
         repeat rewrite Party.eqb_eq in *. rewrite Asset.eqb_eq in *. subst. rewrite H. simpl. repeat rewrite Party.eqb_refl.
         rewrite Asset.eqb_refl. simpl. ring.         
       - symmetry in HeqE2. replace (Party.eqb p2 p1' && Party.eqb p1 p2') with (Party.eqb p1 p2' && Party.eqb p2 p1') by apply andb_comm.
         replace (Party.eqb p2 p2' && Party.eqb p1 p1') with ( Party.eqb p1 p1' && Party.eqb p2 p2') by apply andb_comm.
         rewrite HeqE1. rewrite HeqE2. ring.
Qed.

(** If we combine traces of original contract and the dual one they cancel each other *)
Theorem inverse_dual c env ext tenv trace trace_inv:
  C[|c|] env ext tenv = Some trace ->
  C[|dual c|] env ext tenv = Some trace_inv ->
  add_trace trace trace_inv = empty_trace.
Proof.
  intros. repeat autounfold. repeat (apply functional_extensionality; intro).
  generalize dependent env. generalize dependent x. generalize dependent x0. generalize dependent x1. generalize dependent x2.
  generalize dependent ext.
  generalize dependent trace. generalize dependent trace_inv.
  induction c; intros; simpl in *; option_inv_auto; repeat autounfold in *.
  - ring.
  - assert (x3 = x4) by congruence. subst. erewrite IHc;eauto.
  - unfold singleton_trace. destruct x. apply singleton_trace_inv. autounfold. ring.
  - destruct x7;tryfalse. destruct x8;tryfalse. unfold scale_trace,compose,scale_trans. option_inv_auto.    
    assert (x3 = x5) by congruence. subst.
    replace (x6 x x0 x1 x2 * x5 + x4 x x0 x1 x2 * x5)%R with ((x6 x x0 x1 x2 + x4 x x0 x1 x2)%R * x5)%R by ring.
    rewrite IHc with (env:=env) (ext:=ext); eauto. ring.
  - unfold delay_trace. destruct (Compare_dec.leb (TexprSem t tenv)).
    + eapply IHc;eauto.
    + unfold empty_trans. ring.
  - replace (x5 x x0 x1 x2 + x6 x x0 x1 x2 + (x3 x x0 x1 x2 + x4 x x0 x1 x2))%R with
            (x5 x x0 x1 x2 + x3 x x0 x1 x2 + (x6 x x0 x1 x2 + x4 x x0 x1 x2))%R by ring.
    erewrite IHc1;eauto. erewrite IHc2;eauto. ring.
  - generalize dependent x. generalize dependent ext.
    generalize dependent trace. generalize dependent trace_inv. induction (TexprSem t tenv); intros.
    + simpl in *. destruct (E[|e|] env ext);tryfalse. destruct v; tryfalse.
      destruct b. eapply IHc1; eauto. eapply IHc2; eauto.
    + simpl in *. destruct (E[|e|] env ext);tryfalse. destruct v; tryfalse.
      destruct b.
      * eapply IHc1; eauto.
      * apply liftM_some in H0. apply liftM_some in H. decompose [ex and] H0. decompose [ex and] H. subst.
        unfold delay_trace. destruct (Compare_dec.leb 1 x).
        eapply IHn; eauto. unfold empty_trans. ring.
Qed.
