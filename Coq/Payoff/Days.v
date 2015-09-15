Add LoadPath "..".

Require Import ZArith Arith Syntax Misc Sorting Orders List Utils Denotational Horizon.

Import ListNotations.
Local Coercion is_true : bool >-> Sortclass.

Fixpoint oDaysE (e : Exp) (t : nat) : list nat :=
  match e with 
      | OpE _ es    => concatMap (fun e => oDaysE e t) es
      | Obs _ t'    => [(Z.to_nat t') + t]
      | VarE _      => []
      | Acc e1 _ e2 => oDaysE e1 t ++ oDaysE e2 t
  end.

Fixpoint oDays (c : Contr) (t : nat) : list nat :=
  match c with
    | Scale e c      => oDaysE e t ++ oDays c t
    | Zero           => []
    | Let e c        => oDaysE e t ++ oDays c t
    | Transfer _ _ _ => []
    | Translate _ c  => oDays c t
    | Both c1 c2     => oDays c1 t ++ oDays c2 t
    | If e i c1 c2   => concatMap (oDaysE e) (listFromTo t (t+i)) ++ oDays c1 t ++ oDays c2 (t + i)
  end.

Fixpoint ifDays (count : nat) (l : list nat) :=
  match count with
    | 0 => [l]
    | S n => map (plus (S n)) l :: (ifDays n l)
  end.

Fixpoint tDays (c : Contr) (t : nat) : list nat :=
  match c with
    | Scale e c      => tDays c t
    | Translate t' c => tDays c (t + t')
    | If e t' c1 c2  => flat_map (tDays c1) (listFromNdesc t t') ++ tDays c2 (t + t')
    | Zero           => []
    | Let _ c        => tDays c t
    | Transfer _ _ _ => [t]
    | Both c1 c2     => tDays c1 t ++ tDays c2 t
  end.

Module NatOrder <: TotalLeBool.
  Definition t := nat.
  Definition leb := leb.
  Theorem leb_total : forall a1 a2, leb a1 a2 \/ leb a2 a1.
  Proof.
    intros a1. induction a1 as [| a1']. 
    + left. unfold is_true. reflexivity. 
    + intros a2. destruct a2 as [| a2']. 
      - unfold is_true. simpl. right. reflexivity.
      - simpl. apply IHa1'.
  Qed.
End NatOrder.

Module Import NatSort := Sort NatOrder.

Definition obsDays (c : Contr) : list nat := undup_nat (sort (oDays c 0)).

Definition transfDays (c : Contr) : list nat := undup_nat (sort (tDays c 0)).

Lemma leb_transitive : forall x y z, 
  leb x y -> leb y z -> leb x z.
Proof.
  intros.
  apply leb_iff in H. apply leb_iff in H0. apply leb_iff. 
  apply le_trans with y. apply H. apply H0.
Qed.

Lemma leb_beq_not_beq : forall (x y : nat),
  leb x y -> beq_nat x y = true \/ beq_nat x y = false.
Proof.
  intros x.
  induction x as [| n'].
  + intros. destruct y as [| m'].
    - left. reflexivity.
    - right. reflexivity.
  + intros. destruct y as [| m']. 
    - inversion H.
    - simpl. apply IHn'. simpl in H. apply H.
Qed.


Lemma Forall_tail : forall {X : Type} (x : X) (P: X->Prop) (l : list X),
  Forall P (x :: l) -> Forall P l.
Proof.
  intros. inversion H. apply H3.
Qed.

Lemma Forall_sorted_undup : forall (n m : nat) (l : list nat),
  leb n m -> Forall (leb m) l -> Forall (leb n) (undup_nat l).
Proof.
  intros.
  induction l as [| h l'].
  + intros. apply Forall_nil.
  + intros. simpl. destruct (inb_nat h l').
    - apply IHl'. apply Forall_tail in H0. apply H0.
    - apply Forall_cons. inversion H0. apply leb_transitive with m. apply H. apply H3.
      apply IHl'. apply Forall_tail in H0. apply H0.
Qed.

Lemma unduped_sorted_list_is_sorted : forall l : list nat,
  StronglySorted leb l -> StronglySorted leb (undup_nat l). 
Proof.
  intros. induction H.
  + apply SSorted_nil.
  + simpl. destruct (inb_nat a l).
    - apply IHStronglySorted.
    - inversion H0. simpl. apply SSorted_cons. apply SSorted_nil. apply Forall_nil. 
      apply SSorted_cons. rewrite H3. apply IHStronglySorted.
      apply Forall_sorted_undup with a. apply leb_iff. apply le_refl. 
      apply Forall_cons. apply H1. apply H2.
Qed.

Theorem undup_sort_composition : forall (l : list nat),
  NoRepeat (undup_nat (sort l)) /\ StronglySorted leb (undup_nat (sort l)).
Proof.
  split.
  + apply NoRepeat_undup_nat.
  + apply unduped_sorted_list_is_sorted. apply StronglySorted_sort. 
    unfold Transitive. intros. apply leb_transitive with y. apply H. apply H0.
Qed.

Theorem obsDays_no_repeat_sorted : forall (c : Contr),
  NoRepeat (obsDays c) /\ StronglySorted leb (obsDays c).
Proof.
  intros.
  apply undup_sort_composition.
Qed.

Theorem transDays_no_repeat_sorted : forall (c : Contr),
  NoRepeat (transfDays c) /\ StronglySorted leb (transfDays c).
Proof.
  intros.
  apply undup_sort_composition.
Qed.

Fixpoint obsE (e : Exp) : list ObsLabel :=
  match e with 
      | OpE _ es    => concatMap obsE es
      | Obs lab t'  => [lab]
      | VarE _      => []
      | Acc e1 _ e2 => obsE e1 ++ obsE e2
  end.

Fixpoint obsC (c : Contr): list ObsLabel :=
  match c with
    | Scale e c      => obsE e ++ obsC c
    | Zero           => []
    | Let e c        => obsE e ++ obsC c
    | Transfer _ _ _ => []
    | Translate _ c  => obsC c
    | Both c1 c2     => obsC c1 ++ obsC c2
    | If e i c1 c2   => obsE e ++ obsC c1 ++ obsC c2 
  end.

Lemma plus0_le_Sn : forall (n m : nat),
  plus0 n m <= plus0 (S n) m.
Proof.
  intros.
  generalize dependent n.
  destruct m as [| m'].
  + intros. simpl. apply le_refl.
  + intros. simpl. apply le_S. apply le_refl.
Qed.

Lemma plus0_0_n : forall n : nat,
  plus0 0 n = n.
Proof.
  intros.
  destruct n as [| n']; reflexivity.
Qed.


Lemma lt_plus0 : forall (y x n : nat),
 x < y -> x < plus0 n y.
Proof.
  intros y.
  induction y as [| y'].
  + intros. simpl. apply H.
  + intros. simpl. rewrite plus_comm. apply lt_plus_trans. apply H.
Qed.

Print Contr_rect.

Definition tDays' c := tDays c 0.

Notation "x +? y" := (plus0 x y) (at level 50, left associativity).

Lemma plus0_to_plus : forall n m,
   m <> 0 -> n +? m = n + m.
Proof.
  intros.
  destruct m.
  + contradict H. reflexivity.
  + simpl. reflexivity.
Qed.

Lemma horison_translate_gt_0 : forall c n,
  0 < horizon (Translate n c) -> 0 < horizon c.
Proof.
  intros.
  simpl in H. destruct (horizon c).
  + inversion H.
  + simpl in H. apply lt_0_Sn.
Qed.

Lemma not_0_gt_0 : forall n,
  n <> 0 <-> 0 < n.
Proof.
  split. 
  + intros. destruct n. contradict H. reflexivity. apply lt_0_Sn.
  + intros. unfold not. intros. rewrite H0 in H. contradict H. apply lt_irrefl.
Qed.

Lemma horison_translate_not_0 : forall c n,
  horizon (Translate n c) <> 0 -> horizon c <> 0.
Proof.
  intros. 
  apply not_0_gt_0 in H. apply not_0_gt_0. eapply horison_translate_gt_0. apply H.
Qed.

Lemma max_not_0 : forall n m,
  n <> 0 \/ m <> 0 <-> max n m <> 0.
Proof.
  split.
  + intros. unfold not. intros.
    apply max0 in H0. contradict H0. apply Classical_Prop.or_not_and. apply H.
  + intros. apply Classical_Prop.not_and_or. unfold not. intros. apply H. 
    inversion H0. rewrite H1. rewrite H2. reflexivity.
Qed.

Print Contr_rect.

Lemma n_plus0_max_gt_0 : forall (n m p: nat),
  0 < n -> 0 < m -> 0 < p +? max n m. 
Proof.
  intros.
  simpl. destruct (max n m) eqn: Hmax.
  + apply max0 in Hmax. inversion_clear Hmax. apply lt_0_neq in H. contradict H. symmetry. apply H1.
  + simpl. destruct p. 
    - simpl. apply lt_0_Sn.
    - simpl. apply lt_0_Sn.
Qed.

Lemma n_plus0_max_eq_0 : forall (n m p : nat),
  p +? max n m = 0 -> n = 0 /\ m = 0.
Proof.
  intros. destruct (max n m) eqn: Hmax. 
  + simpl in H. apply max0. assumption.
  + simpl in H. rewrite plus_comm in H. inversion H.
Qed.

Lemma app_nils_is_nil : forall (X : Type) (l1 : list X) (l2 : list X),
  l1 = [] /\ l2 = [] -> l1 ++ l2 = [].
Proof.
  intros. inversion_clear H. rewrite H0. rewrite H1. reflexivity.
Qed.

Lemma flat_map_tDays_empty : forall  (l : list nat) (c : Contr),
 (forall n, tDays c n = []) -> flat_map (tDays c) l = [].
Proof.
  intros.
  induction l as [| h l'].
  + reflexivity.
  + intros. simpl. apply app_nils_is_nil. split. apply H. apply IHl'.
Qed.  

Lemma horizon_zero_empty_days : forall (c : Contr) (n : nat),
  0 = horizon c -> tDays c n = [].
Proof.
  intros c.
  induction c.
  + intros. reflexivity.
  + intros. apply IHc. apply H.
  + intros. inversion H.
  + intros. apply IHc. apply H.
  + intros. simpl. apply IHc. simpl in H. destruct (horizon c).
    - reflexivity.
    - simpl. simpl in H. rewrite <- plus_n_Sm in H. inversion H.
  + intros. simpl. simpl in H. symmetry in H.  apply max0 in H. apply app_nils_is_nil. 
    inversion_clear H as [H1 H2]. split.
    - apply IHc1. symmetry. apply H1.
    - apply IHc2. symmetry. apply H2.
  + intros. simpl. simpl in H. symmetry in H. apply n_plus0_max_eq_0 in H. inversion H. apply app_nils_is_nil. split. 
    - apply flat_map_tDays_empty. intros. apply IHc1. symmetry. apply H0. 
    - apply IHc2. symmetry. apply H1.
Qed.

Lemma In_list_not_empty : forall (X : Type) (x : X) (l : list X),
 In x l -> l <> [].
Proof.
  intros. unfold not. intros. contradict H. rewrite H0. simpl. unfold not. intros. inversion H.
Qed.

Lemma In_tDays_non_zero_horizon : forall (c : Contr) (x n : nat),
  In x (tDays c n) -> horizon c <> 0.
Proof.
  intros.
  apply In_list_not_empty in H. unfold not. intros. apply H. apply horizon_zero_empty_days. symmetry. apply H0.
Qed.

Lemma non_empty_tDays_non_zero_horizon : forall (c : Contr) (n : nat),
  tDays c n <> [] -> horizon c <> 0.
Proof.
  intros. unfold not. intros. apply H. apply horizon_zero_empty_days. symmetry. apply H0.
Qed.

Lemma non_zero_max_non_zero_horizon : forall (c : Contr) (n : nat),
 max_nat_l 0 (tDays c n) <> 0 -> horizon c <> 0.
Proof.
  intros. eapply non_empty_tDays_non_zero_horizon. unfold not. intros. apply H. rewrite H0. reflexivity.
Qed.   
  
Lemma maximum_tDays_n_Sn : forall (c : Contr) (n : nat),
  max_nat_l 0 (tDays c n) <= max_nat_l 0 (tDays c (S n)).
Proof.
  intros.
  generalize dependent n.
  induction c; intros; simpl; try (apply IHc).
  + apply le_refl.
  + rewrite Max.max_0_r. apply le_n_Sn.
  + rewrite maximum_app. rewrite maximum_app. apply NPeano.Nat.max_le_compat. apply IHc1. apply IHc2.
  + rewrite maximum_app. rewrite maximum_app. apply NPeano.Nat.max_le_compat.
    - induction n as [| n']. 
      * simpl. rewrite app_nil_r. rewrite app_nil_r. apply IHc1.
      * simpl. rewrite maximum_app. rewrite maximum_app. apply NPeano.Nat.max_le_compat. apply IHc1. apply IHn'.
    - apply IHc2.
Qed.

Lemma maximum_flat_map_tDays : forall (c : Contr) (t t' : nat),
  max_nat_l 0 (flat_map (tDays c) (listFromNdesc t t')) = max_nat_l 0 (tDays c (t+t')).
Proof.
  intros.
  generalize dependent t.
  induction t' as [| t''].
  + intros. simpl. rewrite app_nil_r. rewrite plus_0_r. reflexivity.
  + intros. simpl. rewrite maximum_app. apply NPeano.Nat.max_l_iff. rewrite IHt''. replace (t + S t'') with ( S (t + t'')). 
    apply maximum_tDays_n_Sn. omega.
Qed.

Lemma plus0_n_not_zero : forall n m,
  n +? m <> 0 -> m <> 0.
Proof.
  intros. destruct m. 
  + contradict H. reflexivity.
  + unfold not. intros. inversion H0.
Qed.

Theorem tDays_lt_horizon : forall (c : Contr) (x n : nat),
  In x (tDays c n) -> x < n + (horizon c).
Proof.
  intros.
  generalize dependent x.
  generalize dependent n.
  induction c.
  + (* Zero *) simpl. intros. inversion H.
  + (* Let *) simpl. intros. apply IHc. apply H.
  + (* Transfer *) simpl. intros. inversion H as [H1 | H2].
    - rewrite H1. rewrite plus_comm. apply lt_n_Sn.
    - inversion H2.
  + (* Scale *) simpl. intros. apply IHc. apply H.
  + (* Translate *) simpl. intros. rewrite plus0_to_plus. rewrite plus_assoc.
    apply (IHc (n0 + n) x). apply H. apply In_tDays_non_zero_horizon in H. apply H.
  + (* Both *) intros. simpl. simpl in *. rewrite <- Max.plus_max_distr_l. apply NPeano.Nat.max_lt_iff.
     apply in_app_iff in H. inversion H as [H1 | H2].
    - left. apply IHc1. apply H1.
    - right. apply IHc2. apply H2.
  + (* If *) intros. simpl. rewrite plus0_to_plus. rewrite plus_assoc. rewrite <- Max.plus_max_distr_l. apply NPeano.Nat.max_lt_iff.
    simpl in H. apply in_app_iff in H. inversion_clear H. left. induction n as [| n'].
    - simpl in H0. rewrite app_nil_r in H0. rewrite plus_0_r. apply IHc1. apply H0.
    - simpl in H0. apply in_app_iff in H0. inversion_clear H0.
      * apply IHc1. apply H.
      * replace (n0 + S n' + horizon c1) with (S (n0 + n' + horizon c1)). apply lt_S. apply IHn'. apply H. omega.
    - right. apply IHc2. apply H0.
    - apply In_tDays_non_zero_horizon in H. simpl in H. apply plus0_n_not_zero in H. apply H.
Qed.

Axiom some_obs : RealObs.
Axiom P1 : Party.
Axiom P2 : Party.
Axiom EUR : Asset.

Definition sampleExp := OpE Cond [OpE Less [(Obs (LabR some_obs) 0%Z); OpE (RLit 10) []]; OpE (RLit 10) []; (Obs (LabR some_obs) 0%Z)].

Definition sampleContr := Translate 5%nat (Scale sampleExp (Transfer P1 P2 EUR)).

Definition optionApp (tr : option Trace) (n : nat) :=
  match tr with
    | Some f => Some (f n)
    | None => None
  end.

Eval compute in (optionApp (Csem sampleContr [] (fun some_obs t => RVal 20)) 5).

Eval compute in (horizon sampleContr).

Example empty_trans_example :  (optionApp (Csem sampleContr [] (fun some_obs t => (RVal 20))) 4%nat = Some empty_trans).
Proof.
reflexivity.
Qed.
