Add LoadPath "..".

Require Import ZArith Arith Syntax Misc Sorting Orders List Utils.

Import ListNotations.
Local Coercion is_true : bool >-> Sortclass.

Fixpoint oDaysE (e : Exp) (t : Z) : list Z :=
  match e with 
      | OpE _ es    => concatMap (fun e => oDaysE e t) es
      | Obs _ t'    => [Zplus t' t]
      | VarE _      => []
      | Acc e1 _ e2 => oDaysE e1 t ++ oDaysE e2 t
  end.

Fixpoint oDays (c : Contr) (t : Z) : list Z :=
  match c with
    | Scale e c      => oDaysE e t ++ oDays c t
    | Zero           => []
    | Let e c        => oDaysE e t ++ oDays c t
    | Transfer _ _ _ => []
    | Translate _ c  => oDays c t
    | Both c1 c2     => oDays c1 t ++ oDays c2 t
    | If e i c1 c2   => concatMap (oDaysE e) (listFromTo t (Zplus t (Z.of_nat i))) ++ oDays c1 t ++ oDays c2 t 
  end.

Fixpoint tDays (c : Contr) (t : Z) : list Z :=
  match c with
    | Scale e c      => tDays c t
    | Translate t' c => tDays c (Zplus (Z.of_nat t') t)
    | If e t' c1 c2  => let date_interv := (listFromTo t (Zplus t (Z.of_nat t'))) in
                        concatMap (tDays c1) date_interv ++ concatMap (tDays c2) date_interv
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

Definition obsDays (c : Contr) : list nat := undup_nat (sort (map Z.to_nat (oDays c 0%Z))).

Definition transfDays (c : Contr) : list nat := undup_nat (sort (map Z.to_nat (tDays c 0%Z))).

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
