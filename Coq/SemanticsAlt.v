Require Export Typing.
Require Export ZArith.
Require Import Equality.
Require Import FunctionalExtensionality.
Require Import Tactics.
Require Export Environments.
Require Import List.
Require Import Denotational.

Import ListNotations.

Definition FinTrace := list Trans.


(* The following are combinators to contruct traces. *)

(*Definition const_trace (t : Trans) : Trace := fun x => t.*)
Definition empty_trace : FinTrace := [].
Definition singleton_trace (t : Trans) : FinTrace
  := [t].

Definition scale_trace (s : R) (t : FinTrace) : FinTrace
  := map (fun tr => scale_trans s tr) t.

(*Lemma scale_trace_0 t : scale_trace 0 t = empty_trace.
Proof.
  unfold scale_trace, empty_trace,compose. apply functional_extensionality. intros.
  simpl. apply scale_trans_0.
Qed.*)

Lemma scale_empty_trace r : scale_trace r empty_trace = empty_trace.
Proof.
  unfold scale_trace, empty_trace. reflexivity.
Qed.

Open Scope nat.

Definition delay_trace (d : nat) (t : FinTrace) : FinTrace :=
  match d with
    | O => t
    | S _ => empty_trans :: t
  end.

(* Fixpoint longZipWith {A} (neutral : A) (f : A -> A -> A) (xs : list A) (ys : list A) : list A := *)
(* match xs, ys with *)
(*     | (x::xs'), (y::ys') => f x y :: longZipWith neutral f xs' ys' *)
(*     | (x::xs'), [] => f x neutral :: longZipWith neutral f xs' [] *)
(*     | [], (y::ys') => f neutral y :: longZipWith neutral f [] ys' *)
(*     | [], [] => [] *)
(* end. *)

(* Definition add_trace (t1 t2 : FinTrace) : FinTrace  *)
(*   := longZipWith add_trans t1 t2. *)
