Require Import List ZArith Arith Sorting Orders Bool.

Import ListNotations.

Definition concatMap {X Y : Type} (f : X -> list Y) (l : list X) : list Y := 
  fold_left (fun x y => app x y) (map f l) [].

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

Definition listFromTo (n : Z) (m : Z) : list Z := scan_left Zplus n (repeat_n 1%Z (Z.to_nat (Zminus m n))).

Example list_from_1_to_5 : listFromTo 2 5 = [2%Z;3%Z;4%Z;5%Z].
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
