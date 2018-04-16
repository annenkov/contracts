(* Add LoadPath "..". *)
Require Import Reals Arith List Sorting Orders Tactics.

Import ListNotations.
Import Omega.

Open Scope nat.

Fixpoint concat {X : Type} (ll : list (list X)) : list X :=

  match ll with
    | [] => []
    | h :: t => h ++ concat t
  end.

Definition concatMap {X Y : Type} (f : X -> list Y) (l : list X) : list Y := 
  concat (map f l).

Example concatMap_singleton_list : (concatMap (fun x => [x]) [1;2;3;4]) = [1;2;3;4].
Proof.
  compute. reflexivity.
Qed.

Example concatMap_double : (concatMap (fun x => [x;x]) [1;2;3;4]) = [1;1;2;2;3;3;4;4].
Proof.
  compute. reflexivity.
Qed.

Fixpoint repeat_n {X : Type} (x : X) (n : nat) :=
  match n with
      | O => []
      | S n' => x :: repeat_n x n'
  end.

Lemma repeat_n_length : forall {X : Type} (x : X) (n : nat),
  length (repeat_n x n) = n.
Proof.
  induction n as [| n'].
  + reflexivity.
  + simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint scan_left {X : Type} (f : X -> X -> X) (a0 : X) (l : list X) : list X :=
  match l with
    | [] => [a0]
    | h :: t => a0 :: scan_left f (f a0 h) t
  end.

Definition listFromTo (n : nat) (m : nat) : list nat := scan_left plus n (repeat_n 1 (m-n)).

Fixpoint listFromNdesc (n : nat) (count : nat) : list nat := 
  match count with
    | O => [n]
    | S n' => n + S n' :: listFromNdesc n n'
end.

Fixpoint listFromNasc (n count : nat) : list nat := 
  match count with
    | O => []
    | S n' => n :: listFromNasc (S n) n'
  end.

Example list_from_2_to_5 : listFromTo 2 5 = [2;3;4;5].
Proof.
  compute. reflexivity.
Qed.

Example list_from_N_desc : listFromNdesc 2 2 = [4;3;2].
Proof.
  compute. reflexivity.
Qed.

Example list_from_N_asc : listFromNasc 2 3 = [2;3;4].
Proof.
  compute. reflexivity.
Qed.

Fixpoint inb_nat (x : nat) (l : list nat) : bool :=
  match l with
    | [] => false
    | h :: t => if (beq_nat h x) then true else inb_nat x t
  end.

Fixpoint undup_nat (l : list nat) : list nat :=
  match l with
    | [] => []
    | h :: t => if (inb_nat h t) then undup_nat t else h :: undup_nat t
   end.

Lemma if_same_branches : forall (X : Type) (b : bool) (x : X),
  (if b then x else x) = x.
Proof.
  intros. induction b. reflexivity. reflexivity.
Qed.

Theorem In_inb : forall (x : nat) (l : list nat),
  In x l <-> inb_nat x l = true.
Proof.
  split.
  intros.
  + induction l as [| h l'].
    - intros. inversion H.
    - intros. simpl. simpl in H. destruct H. 
      * rewrite -> H. rewrite <- beq_nat_refl. reflexivity.
      * rewrite -> IHl'. rewrite -> if_same_branches. reflexivity. apply H.
  + intros. induction l as [| t l'].
    - inversion H.
    - simpl. simpl in H. destruct (beq_nat t x) eqn:Hbeq. 
      * apply beq_nat_true in Hbeq. left. apply Hbeq.
      * right. apply IHl'. apply H. 
Qed.

Lemma not_In_inb_false : forall (x : nat) (l : list nat),
  ~ In x l -> inb_nat x l = false.
Proof.
  intros.
  unfold not in H. induction l as [| h l'].
  + reflexivity.
  + simpl. simpl in H. destruct (beq_nat h x) eqn: Hbeq. 
    - exfalso. apply H. 
      left. apply beq_nat_eq. symmetry. apply Hbeq.
    - simpl. apply IHl'. intros. apply H. right. apply H0.
Qed.

Lemma inb_false_not_In : forall (x : nat) (l : list nat),
  inb_nat x l = false -> ~ In x l.
Proof.
  intros.
  unfold not in H. induction l as [| h l'].
  + unfold not. intros. simpl in H0. apply H0.
  + simpl. unfold not. simpl in H. destruct (beq_nat h x) eqn: Hbeq. 
    - inversion H.
    - simpl. unfold not in IHl'. intros. apply IHl'. apply H. inversion H0. 
      * apply beq_nat_false_iff  in Hbeq. contradict H1. apply Hbeq.
      * apply H1.
Qed.

Inductive NoRepeat {X : Type} : list X -> Prop :=
  | nr_nil : NoRepeat []
  | nr_head : forall (a : X) (l : list X), ~ In a l -> NoRepeat l  -> NoRepeat (a :: l).

Lemma inb_cons_false : forall (x y : nat) (l : list nat),
  inb_nat x (y :: l) = false -> inb_nat x l = false.
Proof.
  intros. simpl in H. destruct (beq_nat y x). inversion H. apply H.
Qed.

Lemma inb_false_undup_false : forall (x : nat) (l : list nat),
  inb_nat x l = false -> inb_nat x (undup_nat l) = false.
Proof.
  intros.
  induction l as [| h l'].
  + reflexivity.
  + simpl. destruct (inb_nat h l').
    - apply IHl'. apply inb_cons_false in H. apply H.
    - simpl. destruct (beq_nat h x) eqn: Hbeq. 
      * inversion H. rewrite Hbeq. reflexivity.
      * simpl. apply IHl'. apply inb_cons_false in H. apply H.
Qed.

Lemma In_undup_list_In_list_iff : forall (x : nat) (l : list nat),
  In x (undup_nat l) <-> In x l.
Proof.
  split. 
  + intros. induction l as [| h l'].
    - inversion H.
    - simpl. simpl in H. destruct (inb_nat h l').
      * right. apply IHl'. apply H.
      * simpl in H. inversion H. left. apply H0. right. apply IHl'. apply H0.
  + intros. induction l as [| h l']. 
    - inversion H.
    - simpl. simpl in H. destruct (inb_nat h l') eqn: Hinb.
      * apply IHl'. inversion H. rewrite H0 in Hinb. apply In_inb in Hinb. apply Hinb. apply H0.
      * simpl. inversion H. left. apply H0. right. apply IHl'. apply H0.
Qed.

Theorem NoRepeat_undup_nat : forall l : list nat,
  NoRepeat (undup_nat l).
Proof.
  intros. induction l as [| h l'].
  + simpl. apply nr_nil.
  + simpl. destruct (inb_nat h l') eqn: Hinb.
    - apply IHl'.
    - apply nr_head. unfold not. intros. apply inb_false_not_In in Hinb. 
      contradict Hinb. apply In_undup_list_In_list_iff. apply H. apply IHl'.
Qed.

Fixpoint max_nat_l (m : nat) (l : list nat) :=
  match l with
    | []     => m
    | h :: t => max h (max_nat_l m t)
  end.

Definition maximum_nat (l : list nat) := max_nat_l 0 l.

Lemma maximum_le : forall (l : list nat) (x n : nat),
  In x l -> x <= max_nat_l n l.
Proof.
  intros l.
  induction l as [| h l'].
  + contradiction.
  + intros. unfold maximum_nat. simpl. simpl in H. apply Nat.max_le_iff. inversion_clear H.
    - left. rewrite H0. apply le_refl.
    - right. apply IHl'. apply H0.
Qed.

Lemma max_eq_snd : forall n m p,
  m = p -> max n m = max n p.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma max_lt_compat : forall n m p q,
  n < p -> m < q -> max n m < max p q.
Proof.
  intros. apply Nat.max_lub_lt_iff. split.
  + apply Nat.max_lt_iff. left. apply H.
  + apply Nat.max_lt_iff. right. apply H0.
Qed.

Lemma maximum_n_le : forall l n,
  n <= max_nat_l n l.
Proof.
  intros l.
  induction l as [| h l'].
  + intros. apply le_refl.
  + intros. simpl. apply Nat.max_le_iff. right. apply IHl'.
Qed.

Lemma maximum_app : forall (l1 l2 : list nat) (n : nat),
  max_nat_l n (l1 ++ l2) = max (max_nat_l n l1) (max_nat_l n l2).
Proof.
  intros l1.
  induction l1 as [| h l'].
  + intros. simpl. symmetry. apply Max.max_r. apply maximum_n_le.
  + intros. unfold maximum_nat. simpl. rewrite <- Max.max_assoc. apply max_eq_snd. apply IHl'.
Qed.

(* Properties of sum of list's elements *)

Definition sum_list xs := fold_right Rplus 0%R xs.

Lemma sum_split : forall l1 l2,
  sum_list (l1 ++ l2) = ((sum_list l1) + (sum_list l2))%R.
Proof.
  induction l1.
  + intros. destruct l2.
    - simpl. rewrite Rplus_0_l. reflexivity.
    - simpl. rewrite Rplus_0_l. reflexivity.
  + intros. simpl. rewrite IHl1. rewrite Rplus_assoc. reflexivity.
Qed.

Lemma seq_split : forall n t0 t,
  seq t0 (n + t) = seq t0 n ++ seq (t0 + n) t.
Proof.
  intro n. induction n.
  + intros. rewrite plus_0_l. rewrite plus_0_r. reflexivity.
  + intros. simpl. apply f_equal. rewrite IHn. replace (t0 + S n) with (S t0 + n). reflexivity.
    omega.
Qed.

Lemma summ_list_common_factor: forall n f x t0 g,
  sum_list (map (fun t : nat => (g t * (f t * x)))%R (seq t0 n)) =
  (x * sum_list (map (fun t : nat => (g t * f t))%R  (seq t0 n)))%R.
Proof.
  induction n.
  + intros. simpl. ring.
  + intros. simpl. rewrite IHn. ring.
Qed.

Lemma summ_list_plus: forall n f g t0 q,
  sum_list (map (fun t : nat => (q t * (f t + g t)))%R (seq t0 n)) =
  (sum_list (map (fun t : nat => (q t * f t)) (seq t0 n)) + sum_list (map (fun t : nat => (q t * g t)) (seq t0 n)))%R.
Proof.
  induction n.
  + intros. simpl. ring.
  + intros. simpl. rewrite IHn. rewrite <- Rplus_assoc. ring. 
Qed.

(* Some lemmas about boolean less-or-equal *)

Lemma plus_leb_compat_l n m p:
  leb m n = true ->
  leb (p + m) (p + n) = true.
Proof.
  intro. apply leb_iff. apply plus_le_compat. apply le_refl. apply leb_iff. assumption.
Qed.

Lemma leb_plus_l n m:
  leb n (n + m) = true.
Proof.
  intros. apply leb_iff. apply le_plus_l.
Qed.

Lemma leb_plus_r n m:
  leb n (m + n) = true.
Proof.
  intros. apply leb_iff. apply le_plus_r.
Qed.

Lemma leb_refl n :
  leb n n = true.
Proof.
  intros. apply leb_iff. apply Nat.le_refl.
Qed.

Lemma beq_nat_leb n m:
  beq_nat m n = true ->
  leb n m = true.
Proof.
  intros. apply beq_nat_true in H. subst. apply leb_refl.
Qed.

Lemma leb_true_beq_false_minus n m:
  beq_nat n m = false ->
  leb n m = true ->
  (0 < (m - n))%nat.
Proof.
  intros. apply beq_nat_false in H. apply leb_iff in H0.
  apply lt_minus_O_lt. apply le_lt_eq_dec in H0. inversion H0. assumption. tryfalse.
Qed.

Open Scope nat.
Lemma le_not_eq_lt: forall (n m : nat),
  n <> m ->
  n <= m ->
  n < m.
Proof.
  intros. apply le_lt_eq_dec in H0. inversion H0. assumption. tryfalse.
Qed.

Lemma leb_n_m_0 n m:
  leb n 0 = true ->
  leb n m = true.
Proof.
  intros. rewrite leb_iff. rewrite leb_iff in H.  apply le_n_0_eq in H. subst. apply le_0_n.
Qed.  

Lemma leb_n_plus_m_true n m:
  leb n (n+m) = true.
Proof.
  apply leb_iff. omega.
Qed.
