(********** Denotational Semantics **********)

Require Export Typing.
Require Export ZArith.
Require Import Equality.
Require Import FunctionalExtensionality.
Require Import Tactics.
Require Export Environments.

Import ListNotations.

(* The type of values for evaluating expressions *)

Inductive Val : Set := BVal : bool -> Val | RVal : R -> Val.


(* Semantics of real expressions. *)

Fixpoint Acc_sem {A} (f : nat -> A -> A) (n : nat) (z : A) : A :=
  match n with
    | O => z
    | S n' => f n (Acc_sem f n' z)
  end.

(* Induction principle for Acc_sem *)
Lemma Acc_sem_ind A (P : A -> Prop) f n z : (forall i (x : A), P x -> P (f i x)) ->  
                                            P z -> P (Acc_sem f n z).
Proof.
  intros F Z. induction n; simpl;auto.
Qed.

(* Semantics of operations *)

Definition OpSem (op : Op) (vs : list Val) : option Val :=
  match op with
    | Add => match vs with ([RVal x; RVal y ]) => Some (RVal (x + y)) | _ => None end
    | Sub => match vs with ([RVal x; RVal y ]) => Some (RVal (x - y)) | _ => None end
    | Mult => match vs with ([RVal x; RVal y ]) => Some (RVal (x * y)) | _ => None end
    | Div => match vs with ([RVal x; RVal y ]) => Some (RVal (x / y)) | _ => None end
    | And => match vs with ([BVal x; BVal y ]) => Some (BVal (x && y)) | _ => None end
    | Or => match vs with ([BVal x; BVal y ]) => Some (BVal (x || y)) | _ => None end
    | Less => match vs with ([RVal x; RVal y ]) => Some (BVal (Rltb x y)) | _ => None end
    | Leq => match vs with ([RVal x; RVal y ]) => Some (BVal (Rleb x y)) | _ => None end
    | Equal => match vs with ([RVal x; RVal y ]) => Some (BVal (Reqb x y)) | _ => None end
    | BLit b => match vs with ([]) => Some (BVal b) | _ => None end
    | RLit r => match vs with ([]) => Some (RVal r) | _ => None end
    | Cond => match vs with
                | ([BVal b; RVal x; RVal y ]) => Some (RVal (if b then x else y))
                | ([BVal b; BVal x; BVal y ]) => Some (BVal (if b then x else y))
                | _ => None end
    | Neg => match vs with ([RVal x]) => Some (RVal (0 - x) %R) | _ => None end
    | Not => match vs with ([BVal x]) => Some (BVal (negb x)) | _ => None end
  end.



Definition ExtEnv := ExtEnv' Val.

(* (Internal) environments map variables to values. *)

Definition Env := Env' Val.

(* Semantics of expressions. *)

Reserved Notation "'E[|' e '|]'" (at level 9).

Definition Fsem {A} (f : Env -> ExtEnv -> option A) (env : Env) (ext : ExtEnv) 
  := (fun m x => x >>= fun x' =>  f (x' :: env) (adv_ext (Z.of_nat m) ext)).

Fixpoint Esem (e : Exp) (env : Env) (ext : ExtEnv) : option Val :=
    match e with
      | OpE op args => sequence (map (fun e => E[|e|] env ext) args) >>= OpSem op
      | Obs l i => Some (ext l i)
      | VarE v => lookupEnv v env
      | Acc f l z => let ext' := adv_ext (- Z.of_nat l) ext
                     in Acc_sem (Fsem E[|f|] env ext') l (E[|z|] env ext')
    end
      where "'E[|' e '|]'" := (Esem e ). 


(* Semantic structures for contracts. *)

(* An elemtn of type [trans] represents a set of Transfers that a
 contract specifies at a particular point in time. It can also be
 [None], which indicates that the set of Transfers is undefined (read:
 "bottom"). *)

Definition Trans := Party -> Party -> Asset -> R.


Open Scope R.
Definition empty_trans : Trans := fun p1 p2 c => 0.
Definition singleton_trans (p1 p2 : Party) (a : Asset) r : Trans
  := if Party.eqb p1 p2 then (fun p1' p2' a' => 0) else
       fun p1' p2' a' => if Party.eqb p1 p1' && Party.eqb p2 p2' && Asset.eqb a a'
                            then r
                            else if Party.eqb p1 p2' && Party.eqb p2 p1' && Asset.eqb a a'
                                 then -r
                                 else 0.
Definition add_trans : Trans -> Trans -> Trans := fun t1 t2 p1 p2 c => (t1 p1 p2 c + t2 p1 p2 c).
Definition scale_trans : R -> Trans -> Trans := fun s t p1 p2 c => (t p1 p2 c * s).

Lemma scale_empty_trans r : scale_trans r empty_trans = empty_trans.
Proof.
  unfold scale_trans, empty_trans. rewrite Rmult_0_l. reflexivity.
Qed.

Lemma scale_trans_0 t : scale_trans 0 t = empty_trans.
Proof.
  unfold scale_trans, empty_trans. do 3 (apply functional_extensionality;intro). rewrite Rmult_0_r. reflexivity.
Qed.


Lemma add_trans_comm t1 t2 : add_trans t1 t2 = add_trans t2 t1.
Proof.
 do 3 (apply functional_extensionality;intro). unfold add_trans. ring.
Qed.

Lemma add_empty_trans_l t : add_trans empty_trans t = t.
Proof.
  unfold add_trans, empty_trans. do 3 (apply functional_extensionality;intro). ring.
Qed.

Lemma add_empty_trans_r t : add_trans t empty_trans = t.
Proof.
  unfold add_trans, empty_trans. do 3 (apply functional_extensionality;intro). ring.
Qed.

Lemma add_trans_scale_distr t1 t2 r :
  scale_trans r (add_trans t1 t2) = (add_trans (scale_trans r t1) (scale_trans r t2)).
Proof.
  do 3 (apply functional_extensionality;intro). unfold add_trans,scale_trans. ring.
Qed.

Hint Resolve scale_empty_trans add_empty_trans_l add_empty_trans_r.

(* Traces represent the sequence of obligations that a contract
specifies. *)

Definition Trace := nat -> Trans.



(* The following are combinators to contruct traces. *)

Definition const_trace (t : Trans) : Trace := fun x => t.
Definition empty_trace : Trace := const_trace empty_trans.
Definition singleton_trace (t : Trans) : Trace
  := fun x => match x with 
                | O => t
                | _ => empty_trans
              end.
Definition scale_trace (s : R) (t : Trace) : Trace
  := scale_trans s ∘ t.

Lemma scale_trace_0 t : scale_trace 0 t = empty_trace.
Proof.
  unfold scale_trace, empty_trace,compose. apply functional_extensionality. intros.
  simpl. apply scale_trans_0.
Qed.

Lemma scale_empty_trace r : scale_trace r empty_trace = empty_trace.
Proof.
  unfold scale_trace, empty_trace,compose. apply functional_extensionality. intros.
  simpl. apply scale_empty_trans.
Qed.


Open Scope nat.

Definition delay_trace (d : nat) (t : Trace) : Trace :=
  fun x => if leb d x
           then t (x - d)
           else empty_trans.

Definition add_trace (t1 t2 : Trace) : Trace 
  := fun x => add_trans (t1 x) (t2 x).

Lemma add_trace_comm t1 t2 : add_trace t1 t2 = add_trace t2 t1.
Proof.
  apply functional_extensionality;intro. apply add_trans_comm.
Qed.

Lemma add_empty_trace_l t : add_trace empty_trace t = t.
Proof.
  unfold add_trace, empty_trace. apply functional_extensionality;intro. apply add_empty_trans_l.
Qed.

Lemma add_empty_trace_r t : add_trace t empty_trace = t.
Proof.
  unfold add_trace, empty_trace. apply functional_extensionality;intro. apply add_empty_trans_r.
Qed.

Lemma add_trace_scale_distsr r t1 t2 :
  scale_trace r (add_trace t1 t2) = (add_trace (scale_trace r t1) (scale_trace r t2)).
Proof.
  apply functional_extensionality;intro. apply add_trans_scale_distr.
Qed.


(* Some lemmas about [delay_trace]. *)

Lemma delay_trace_0 t : delay_trace 0 t = t.
Proof.
  apply functional_extensionality.
  unfold delay_trace. simpl. intros. f_equal. omega.
Qed.

Lemma delay_trace_S n i x: delay_trace (S n) x (S i) = delay_trace n x i.
Proof.
  unfold delay_trace,compose. cases (leb (S n) (S i)); simpl in Eq; rewrite Eq; reflexivity.
Qed.


Lemma delay_empty_trace r : delay_trace r empty_trace = empty_trace.
Proof.
  apply functional_extensionality. intros. 
  unfold delay_trace, empty_trace,const_trace. destruct (leb r x);reflexivity.
Qed.

Lemma delay_trace_iter d d' t : delay_trace d (delay_trace d' t) = delay_trace (d' + d) t.
Proof.
  apply functional_extensionality. induction d'; intros.
  simpl. rewrite delay_trace_0. reflexivity.
  simpl. unfold delay_trace in *. 
  remember (leb d x) as L. destruct L;
  remember (leb (S d') (x - d)) as L1; destruct L1;
  remember (leb (S (d' + d)) x) as L2; destruct L2;
  symmetry in HeqL; symmetry in HeqL1;  symmetry in HeqL2;
 
  try apply leb_complete in HeqL; try apply leb_complete in HeqL1;
  try apply leb_complete in HeqL2;
  try apply leb_complete_conv in HeqL; try apply leb_complete_conv in HeqL1;
  try apply leb_complete_conv in HeqL2; f_equal; try omega; try reflexivity.
Qed.


Lemma delay_trace_swap d d' e : 
  delay_trace d (delay_trace d' e) = delay_trace d' (delay_trace d e).
Proof.
  repeat rewrite delay_trace_iter. rewrite plus_comm. reflexivity.
Qed.

Lemma delay_trace_add d t1 t2 :
  delay_trace d (add_trace t1 t2) = add_trace (delay_trace d t1) (delay_trace d t2).
Proof.
  unfold delay_trace,add_trace. apply functional_extensionality. intro x.
  destruct (leb d x).
  reflexivity.
  symmetry.  auto.
Qed.


Lemma delay_trace_scale d r tr : delay_trace d (scale_trace r tr) = scale_trace r (delay_trace d tr).
Proof.
  unfold delay_trace.
  unfold delay_trace,scale_trace,compose. apply functional_extensionality. intro x.
  destruct (leb d x).
  reflexivity.
  symmetry. apply scale_empty_trans.
Qed.

(* The following function is needed to define the semantics of [IfWithin]. *)

Fixpoint within_sem (c1 c2 : Env -> ExtEnv -> TEnv -> option Trace) 
         (e : Exp) (i : nat)  (env : Env) (rc : ExtEnv) (tenv : TEnv) : option Trace 
  := match E[|e|] env rc with
       | Some (BVal true) => c1 env rc tenv
       | Some (BVal false) => match i with
                         | O => c2 env rc tenv
                         | S j => liftM (delay_trace 1) (within_sem c1 c2 e j env (adv_ext 1 rc) tenv)
                       end
       | _ => None
     end.


(* Semantics of contracts. *)

Reserved Notation "'C[|' e '|]'" (at level 9).

Definition toReal (v : Val) : option R := 
  match v with
    | RVal r => Some r
    | _ => None
  end.

(* Semantics for template expressions *)
Definition TexprSem (e : TExpr) (tenv : TEnv) : nat :=
  match e with
    | Tvar v => tenv v
    | Tnum n => n
  end.

Fixpoint Csem (c : Contr) (env : Env) (ext : ExtEnv) (tenv : TEnv) : option Trace :=
    match c with
      | Zero => Some empty_trace
      | Let e c => E[|e|] env ext >>= fun val => C[|c|] (val :: env) ext tenv
      | Transfer p1 p2 c => Some (singleton_trace (singleton_trans p1 p2 c 1))
      | Scale e c' => liftM2 scale_trace (E[|e|] env ext >>= toReal) (C[|c'|] env ext tenv)
      | Translate v c' => liftM (delay_trace (TexprSem v tenv)) (C[|c'|]env (adv_ext (Z.of_nat (TexprSem v tenv)) ext) tenv)
      | Both c1 c2 => liftM2 add_trace (C[|c1|]env ext tenv) (C[|c2|]env ext tenv)
      | If e d c1 c2 => within_sem C[|c1|] C[|c2|] e (TexprSem d tenv) env ext tenv
    end
      where "'C[|' e '|]'" := (Csem e).
