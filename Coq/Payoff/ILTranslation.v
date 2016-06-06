Add LoadPath "..".

Require Import Tactics.
Require Import ILSyntax.
Require Import ILSemantics.
Require Import Denotational.
Require Import Syntax.
Require Import Utils.
Require Import Horizon.
Require Import Misc.
Require Import Reduction.

Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import FunctionalExtensionality.
Require Import Coq.Program.Equality.

Import ListNotations.

Local Open Scope Z.

Definition tsmartPlus e1 e2 :=
  match e1 with
    | ILTexpr (Tnum 0) => e2
    | _ => ILTplus e1 e2
  end.

Lemma tsmartPlus_sound e1 e2 tenv:
  ILTexprSem (tsmartPlus e1 e2) tenv = ILTexprSem (ILTplus e1 e2) tenv.
Proof.
  destruct e1; try (destruct e); try (destruct n); reflexivity.
Qed.

Fixpoint fromExp (t0 : ILTExprZ) (e : Exp) :=
  match e with
    | OpE Add [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILAdd v1 v2)))
    | OpE Sub [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILSub v1 v2)))
    | OpE Mult [a1;a2] => (fromExp t0 a1) >>= fun v1 =>
                             (fromExp t0 a2) >>= fun v2 => pure (ILBinExpr ILMult v1 v2)
    | OpE Div [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILDiv v1 v2)))
    | OpE And [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILAnd v1 v2)))
    | OpE Or [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILOr v1 v2)))
    | OpE Less [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILLess v1 v2)))
    | OpE Leq [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                           (fromExp t0 a2) >>= (fun v2 =>
                             pure (ILBinExpr ILLeq v1 v2)))
    | OpE Equal [a1;a2] => (fromExp t0 a1) >>= (fun v1 =>
                             (fromExp t0 a2) >>= (fun v2 =>
                               pure (ILBinExpr ILEqual v1 v2)))
    | OpE Not [a] => fromExp t0 a >>=
                             fun v1 => pure (ILUnExpr ILNot v1)
    | OpE Neg [a] => fromExp t0 a >>=
                             fun v1 => pure (ILUnExpr ILNeg v1)
    | OpE Cond [b;a1;a2] => (fromExp t0 b) >>= (fun b_il =>
                             (fromExp t0 a1) >>= (fun v1 =>
                                (fromExp t0 a2) >>= (fun v2 =>
                                  pure (ILIf b_il v1 v2))))
    | OpE (RLit v) _ => Some (FloatV v)
    | OpE _ _ => None
    | Obs lab t => Some (Model lab (ILTplusZ (ILTnumZ t) t0))
    | VarE n => None
    | Acc _ _ _ => None
  end.
(*
Fixpoint pushForward (t : nat) (e : ILExpr) : ILExpr :=
  match e with
    | ILIf b e1 e2 => ILIf (pushForward t b) (pushForward t e1) (pushForward t e2)
    | Model s t' => match t' with
                           | ILTnumZ i :: t'' => Model s (ILTnumZ i :: ILTnumZ (Z.of_nat t) :: t'')
                           | _ => Model s (ILTnum t :: t')
                    end
    | ILUnExpr op e1 => ILUnExpr op (pushForward t e1)
    | ILBinExpr op e1 e2 => ILBinExpr op (pushForward t e1) (pushForward t e2)
    | FloatV v => FloatV v
    | Payoff t' p1 p2 => match t' with
                           | ILTnumZ i :: t'' => Payoff (ILTnumZ (Z.of_nat t) :: ILTnumZ i :: t'') p1 p2
                           | _ => Payoff (ILTnumZ (Z.of_nat t) :: t') p1 p2
                         end
  end.

Fixpoint nestedIfs (cond : ILExpr) (t' : nat)
                   (c1 : ILExpr) (c2 : ILExpr) : ILExpr :=
  match t' with
    | 0 => ILIf cond c1 c2
    | S t'' => ILIf cond c1
                    (nestedIfs (pushForward 1 cond) t'' (pushForward 1 c1) (pushForward 1 c2))
  end.
 *)


Fixpoint fromContr (c : Contr) (t0 : ILTExpr) : option ILExpr:=
  match c with
    | Scale e c      => fromExp (ILTexprZ t0) e
                                >>= fun v => (fromContr c t0)
                                               >>= fun v' => pure (ILBinExpr ILMult v v')                          
    | Translate t' c => fromContr c (tsmartPlus (ILTexpr t') t0)
    | If e t' c1 c2  => (fromContr c1 t0)
                          >>= fun v1 => (fromContr c2 t0)
                                          >>= fun v2 => fromExp (ILTexprZ t0) e
                                                                >>= fun e => Some (ILLoopIf e v1 v2 t')
    | Zero           => Some (FloatV 0)
    | Let e c        => None
    | Transfer p1 p2 _ => Some (if (Party.eqb p1 p2) then (FloatV 0)
                                else (Payoff t0 p1 p2))
    | Both c1 c2     => (fromContr c1 t0)
                          >>= fun v1 => (fromContr c2 t0)
                                          >>= fun v2 => pure (ILBinExpr ILAdd v1 v2)
  end.

Lemma all_to_forall1 {A} P (x : A) :
  all P [x] -> P x.
Proof.
  intros. inversion H. subst. assumption.
Qed.
     
Lemma all_to_forall2 {A} P (x1 : A) (x2 : A) :
  all P [x1;x2] -> P x1 /\ P x2.
Proof.
  intros. inversion H. subst. split.
  - assumption.
  - apply all_to_forall1 in H3. assumption.
Qed.

Lemma all_to_forall3 {A} P (x1 x2 x3 : A) :
  all P [x1;x2;x3] -> P x1 /\ P x2 /\ P x3.
Proof.
  intros. inversion H. subst. split.
  - assumption.
  - apply all_to_forall2 in H3. assumption.
Qed.

(* Next lemmas look wierd, but I found them helpful for the proof automation*)
Lemma fromVal_RVal_f_eq f x1 x2 y1 y2:
  fromVal (RVal x1) = ILRVal y1 ->
  fromVal (RVal x2) = ILRVal y2 ->
  fromVal (RVal (f x1 x2)) = (ILRVal (f y1 y2)).
Proof.
  intros. simpl in *. inversion H. inversion H0. subst. reflexivity.
Qed.

Lemma ILRVal_zero_mult_l x1 x2:
  ILRVal x1 = ILRVal 0 -> ILRVal (x1 * x2) = ILRVal 0.
Proof.
  intros. inversion H. rewrite Rmult_0_l. reflexivity.
Qed.

Lemma ILRVal_zero_mult_r x1 x2:
  ILRVal x2 = ILRVal 0 -> ILRVal (x1 * x2) = ILRVal 0.
Proof.
  intros. inversion H. rewrite Rmult_0_r. reflexivity.
Qed.

Lemma fromVal_BVal_f_eq f x1 x2 y1 y2:
  fromVal (BVal x1) = ILBVal y1 ->
  fromVal (BVal x2) = ILBVal y2 ->
  fromVal (BVal (f x1 x2)) = (ILBVal (f y1 y2)).
Proof.
  intros. simpl in *. inversion H. inversion H0. subst. reflexivity.
Qed.

Lemma fromVal_BVal_f_eq' f x1 x2 y1 y2:
  fromVal (RVal x1) = ILRVal y1 ->
  fromVal (RVal x2) = ILRVal y2 ->
  fromVal (BVal (f x1 x2)) = (ILBVal (f y1 y2)).
Proof.
  intros. simpl in *. inversion H. inversion H0. subst. reflexivity.
Qed.

Lemma fromVal_BVal_f_eq_un f x1 y1:
  fromVal (BVal x1) = ILBVal y1 ->
  fromVal (BVal (f x1)) = ILBVal (f y1).
Proof.
  intros. simpl in *. inversion H. reflexivity.
Qed.

Lemma fromVal_RVal_un_minus_eq x1 y1:
  fromVal (RVal x1) = ILRVal y1 ->
  fromVal (RVal ( - x1)) = ILRVal ( - y1).
Proof.
  intros. simpl in *. inversion H. reflexivity.
Qed.


Hint Resolve of_nat_succ fromVal_RVal_f_eq fromVal_BVal_f_eq fromVal_BVal_f_eq'.
Hint Resolve fromVal_BVal_f_eq_un fromVal_RVal_un_minus_eq.
Hint Unfold liftM compose bind pure.
Hint Rewrite Nat2Z.inj_succ Rminus_0_l.


Ltac destruct_vals := repeat (match goal with
                        | [x : Val |- _] => destruct x; tryfalse
                        | [x : ILVal |- _] => destruct x; tryfalse
                              end).

Ltac some_inv := repeat (unfold pure in *; match goal with
                   | [H: Some _ = Some _ |- _] => inversion H; clear H
                                           end).

Notation "'IL[|' e '|]'" := (ILsem e).

Ltac destruct_ILsem := repeat (match goal with
                                  | [_ : match IL[|?e|] ?env ?ext ?d ?p1 ?p2  : _ with _ => _ end = _ |- _] =>
                                    let newH := fresh "H" in destruct (IL[|e|] env ext d p1 p2) eqn: newH; tryfalse
                               end).

Hint Unfold ILTexprSem.

Theorem Exp_translation_sound : forall (e : Exp) (il_e : ILExpr) (envC : Env' Val) (extC : ExtEnv' Val)
                                          (extIL : ExtEnv' ILVal) (envT : TEnv)
                                          (v : Val) (v' : ILVal) p1 p2 t0 t0' disc,
  fromExp t0 e = Some il_e ->
  (forall l t, fromVal (extC l t) = extIL l t) ->
  E[|e|] envC (adv_ext (ILTexprSemZ t0 envT + Z.of_nat t0') extC) = Some v ->
  IL[|il_e|] extIL envT t0' disc p1 p2 = Some v'->
  fromVal v = v'.
Proof.
  intros. generalize dependent envC. generalize dependent extC.
  generalize dependent extIL. generalize dependent envT.
  generalize dependent il_e. generalize dependent v. generalize dependent v'.

  induction e using Exp_ind'.
  + (* OpE *)
    intros v' v il_e Htrans extIL envT Hilsem extC Heqext envC Hesem. destruct op;
      (* Binary operations *)
    try (simpl in *; do 3 try (destruct args; tryfalse); tryfalse; simpl in *;
         option_inv_auto; subst; simpl in *; try (some_inv); subst; simpl in *; subst;
         option_inv_auto; subst; simpl in *; destruct_vals;
         subst; option_inv_auto;
         apply all_to_forall2 in H; inversion_clear H;
         eauto);
    (* Unary operations*)
    try (simpl in *; do 2 try (destruct args; tryfalse); tryfalse; simpl in *;
    option_inv_auto; subst; simpl in *; some_inv; subst; simpl in *; subst;
    option_inv_auto; subst; simpl in *; destruct_vals; some_inv; subst; simpl in H6; some_inv; subst;
    apply all_to_forall1 in H; some_inv; autorewrite with core; eauto).
    
    (* Lit *)
    simpl in *. destruct args; tryfalse; simpl in *; option_inv_auto; tryfalse; subst; simpl in *; some_inv; subst. reflexivity.
    
    (* cond *)
    simpl in *. do 4 try (destruct args; tryfalse); tryfalse; simpl in *;
    eapply all_to_forall3 in H; inversion_clear H as [IHe1 IHe']; inversion_clear IHe' as [IHe2 IHe3];
    option_inv_auto; subst; simpl in *; try (some_inv); subst.
    simpl in *; subst; option_inv_auto; subst; simpl in *. destruct x0; tryfalse.    
    destruct x;tryfalse.
    (* Bool *)
    * destruct x1; tryfalse. some_inv; destruct b.
      - (* condition is true*)
      replace x3 with (fromVal (BVal true)) in H8; simpl in H8; eauto.    
      - (* condition is false *)replace x3 with (fromVal (BVal false)) in H8; simpl in H8; eauto.
    (* Real *)
     * destruct x1; tryfalse. some_inv; destruct b.
      - (* condition is true*)
      replace x3 with (fromVal (BVal true)) in H8; simpl in H8; eauto.    
      - (* condition is false *)replace x3 with (fromVal (BVal false)) in H8; simpl in H8; eauto.
    
  + (* Obs *)
    intros. simpl in *. some_inv. subst. simpl in *. some_inv. subst.
    replace (Z.of_nat t0' + (i + ILTexprSemZ t0 envT)) with (ILTexprSemZ t0 envT + Z.of_nat t0' + i). eapply H0. ring.
  + (* Var *)
    intros. inversion H.
  + (* Acc *)
    intros. inversion H.
Qed.

Lemma delay_scale_trace tr t n :
  scale_trace n (delay_trace t tr) = delay_trace t (scale_trace n tr).
Proof.
  unfold scale_trace, delay_trace, compose. apply functional_extensionality. intros. destruct (Compare_dec.leb t x).
  - reflexivity.
  - apply scale_empty_trans.
Qed.

Local Open Scope nat.

Lemma delay_trace_n_m n m tr :
  n <= m ->
  (delay_trace n tr) m = tr (m-n).
Proof.
  intros. unfold delay_trace.
  apply leb_iff in H. rewrite H. reflexivity.
Qed.

Lemma delay_trace_empty_before_n n tr t:
  t < n ->
  (delay_trace n tr) t = empty_trans.
Proof.
  intros. unfold delay_trace. apply leb_correct_conv in H. rewrite H. reflexivity.
Qed.

Lemma sum_of_map_empty_trace : forall n n0 p1 p2 curr trace f,
  trace = empty_trace ->
  sum_list (map (fun t => (f t * trace t p1 p2 curr)%R) (seq n0 n)) = 0%R.
Proof.
  induction n.
  + intros. reflexivity.
  + intros. simpl. rewrite IHn. rewrite H. unfold empty_trace, const_trace, empty_trans. ring. assumption.
Qed.

Lemma delay_trace_zero_before_n : forall n tr p1 p2 curr t0 f,
  sum_list (map (fun t1 : nat => (f t1 * (delay_trace (n + t0) tr t1 p1 p2 curr))%R) (seq t0 n)) = 0%R.
Proof.
  induction n.
  + intros. reflexivity.
  + intros. simpl. rewrite delay_trace_empty_before_n. unfold empty_trans. rewrite Rmult_0_r.
    rewrite Rplus_0_l. replace (S (n + t0)) with (n + S t0).
    apply IHn. omega. rewrite <- plus_Sn_m. omega.
Qed.

Lemma sum_delay t0 t n tr p1 p2 curr f:
  sum_list (map (fun t => (f t * (delay_trace (n + t0) tr) t p1 p2 curr)%R) (seq t0 (n + t))) =
  sum_list (map (fun t => (f t * (delay_trace (n + t0) tr) t p1 p2 curr)%R) (seq (n + t0) t)).
Proof.
  rewrite seq_split. rewrite map_app. rewrite sum_split. rewrite delay_trace_zero_before_n. rewrite Rplus_0_l. rewrite plus_comm. reflexivity.
Qed.

(*Lemma delay_trace_plus n n0 tr t0:
  delay_trace (n + n0) tr (t0 + n0) = delay_trace n tr t0.
Proof.
  destruct n.
  - simpl. destruct t0.
    + rewrite Equivalence.delay_trace_at. rewrite delay_trace_0. reflexivity.
    + simpl. rewrite delay_trace_0. rewrite delay_trace_S.
 *)

Lemma sum_delay' n tr p1 p2 curr f t0 n1:
  sum_list (map (fun t : nat =>(f t * delay_trace (1 + n) tr t p1 p2 curr)%R) (seq (t0 + 1) n1)) =
  sum_list (map (fun t : nat => (f (1 + t)%nat * delay_trace n tr t p1 p2 curr)%R) (seq t0 n1)).
Proof.
  generalize dependent t0. generalize dependent n1.
  induction n.
  - intros. simpl. generalize dependent t0. induction n1; intros.
    + reflexivity.
    + simpl. f_equal.
      * rewrite plus_comm. simpl. rewrite delay_trace_S. reflexivity.
      * rewrite plus_comm. simpl. rewrite <- IHn1. rewrite plus_comm. reflexivity.
  - generalize dependent n. induction n1; intros.
    + reflexivity.
    + rewrite plus_comm. simpl. f_equal.
      * rewrite plus_comm. simpl. rewrite delay_trace_S. rewrite plus_comm. reflexivity.
      * rewrite <- IHn1. simpl. rewrite plus_comm. simpl. reflexivity.
Qed.

(*
Lemma sum_delay' n tr p1 p2 curr f t0 n0 n1:
  sum_list (map (fun t : nat =>(f t * delay_trace (n0 + n) tr t p1 p2 curr)%R) (seq (t0 + n0) (n + n1))) =
  sum_list (map (fun t : nat => (f (n0 + t)%nat * delay_trace n tr t p1 p2 curr)%R) (seq t0 (n + n1))).
Proof.
  generalize dependent t0. generalize dependent n0.
  induction n.
  - intros. destruct n0.
    + simpl. rewrite plus_0_r. reflexivity.
    + simpl.
  - intros; simpl. replace (S (n+n0)) with (S n + n0). rewrite delay_trace_S. f_equal. apply IHn.
Admitted.
*)

Lemma zero_horizon_empty_trans c t trace env ext tenv:
  horizon c tenv = 0 ->
  C[|c|] env ext tenv = Some trace ->
  trace t = empty_trans.
Proof.
  intros. eapply horizon_sound with (c := c) (tenv := tenv). rewrite H. omega. eassumption.
Qed.

Lemma zero_horizon_empty_trace c trace env ext tenv:
  horizon c tenv = 0 ->
  C[|c|] env ext tenv= Some trace ->
  trace = empty_trace.
Proof.
  intros. apply functional_extensionality. intros.
  eapply horizon_sound with (c := c) (tenv := tenv). rewrite H. omega. eassumption.
Qed.

Lemma zero_horizon_delay_trace c m trace env ext tenv:
  horizon c tenv= 0 ->
  C[|c|] env ext tenv = Some trace ->
  delay_trace m trace = trace.
Proof.
  intros. apply functional_extensionality. intros. unfold delay_trace. destruct (Compare_dec.leb m x).
  - erewrite zero_horizon_empty_trans. erewrite zero_horizon_empty_trans. reflexivity.
    eassumption. eassumption. eassumption. eassumption.
  - erewrite zero_horizon_empty_trans. reflexivity. eassumption. eassumption.
Qed.
  
Lemma sum_list_zero_horizon : forall n c t env ext trace p1 p2 curr f tenv,
  horizon c tenv= 0 ->
  C[|c|] env ext tenv = Some trace ->
  sum_list (map (fun t => (f t * trace t p1 p2 curr)%R) (seq t n)) = 0%R.
Proof.
  induction n.
  + intros. reflexivity.
  + intros. simpl. erewrite IHn. erewrite zero_horizon_empty_trans. unfold empty_trans. ring.
    eassumption. eassumption. eassumption. eassumption.
Qed.

Lemma sum_after_horizon_zero : forall n t0 c trace p1 p2 curr ext env tenv,
  C[|c|] env ext tenv = Some trace ->                               
  sum_list (map (fun t => trace t p1 p2 curr) (seq (t0 + horizon c tenv) n)) = 0%R.
Proof.
  intros n.
  induction n.
  + intros. reflexivity.
  + intros. simpl. erewrite horizon_sound. unfold empty_trans.
    rewrite <- plus_Sn_m. erewrite IHn. ring.
    eassumption. instantiate (1:=tenv). instantiate (1:=c). omega. eassumption.
Qed.

Lemma sum_delay_after_horizon_zero : forall n m t0 c trace p1 p2 curr ext env f tenv,
  m <= t0 ->
  C[|c|] env ext tenv= Some trace ->                               
  sum_list (map (fun t => (f t * delay_trace m trace t p1 p2 curr)%R) (seq (t0 + horizon c tenv) n)) = 0%R.
Proof.
  intros n.
  induction n.
  + intros. reflexivity.
  + intros. simpl. rewrite delay_trace_n_m. erewrite horizon_sound. unfold empty_trans.
    rewrite <- plus_Sn_m. erewrite IHn. ring. omega. eassumption.
    instantiate (1:=tenv). instantiate (1:=c). omega. eassumption. omega.
Qed.

Lemma sum_before_after_horizon t0 t c trace p1 p2 curr ext env f tenv:
  C[|c|] env ext tenv = Some trace ->
  sum_list (map (fun t => (f t * (delay_trace t0 trace) t p1 p2 curr))%R (seq t0 (horizon c tenv + t))) =
  sum_list (map (fun t => (f t * (delay_trace t0 trace) t p1 p2 curr))%R (seq t0 (horizon c tenv))).
Proof.
  intros. rewrite seq_split. rewrite map_app. rewrite sum_split. erewrite sum_delay_after_horizon_zero. ring.
  omega. eassumption.
Qed.

Lemma delay_add_trace n tr1 tr2:
      add_trace (delay_trace n tr1) (delay_trace n tr2) = delay_trace n (add_trace tr1 tr2).
Proof.
  unfold add_trace, delay_trace, compose. apply functional_extensionality. intros. destruct (Compare_dec.leb n x).
  - reflexivity.
  - rewrite add_empty_trans_l. reflexivity.
Qed.

Lemma map_delay_trace : forall n m t0 x0 p1 p2 curr,
  m <= t0 ->
  map (fun t : nat => delay_trace m x0 t p1 p2 curr) (seq t0 n) =
  map (fun t : nat => x0 (t-m) p1 p2 curr) (seq t0 n).
Proof.
  induction n.
  - reflexivity.
  - intros. simpl. rewrite delay_trace_n_m. apply f_equal. apply IHn. omega. omega.
Qed.  

Ltac destruct_option_vals := repeat (match goal with
                        | [x : match ?X : option Val with _ => _ end = _ |- _] => destruct X; tryfalse
                        | [x : match ?X : option ILVal with _ => _ end = _ |- _]  => destruct X; tryfalse
                                     end).

Ltac rewrite_option := repeat (match goal with
                        | [H : _ : option ?X  |- match _ : option ?X with _ => _ end = _] => rewrite H
                      end).

Definition translation_sound c envC extC t0 t0' := forall (il_e : ILExpr)
                                        (extIL : ExtEnv' ILVal)
                                        (v' : ILVal) p1 p2 curr v trace (disc : nat -> R ) tenv,
  (forall a a', Asset.eqb a a' = true) ->
  (forall l t, fromVal (extC l t) = extIL l t) ->
  fromContr c t0 = Some il_e ->
  C[|Translate (Tnum (ILTexprSem t0 tenv + t0')) c|] envC extC tenv = Some trace ->
  sum_list (map (fun t => (disc t * trace t p1 p2 curr)%R)
                (seq (ILTexprSem t0 tenv + t0') (horizon c tenv))) = v ->
  (IL[|il_e|] extIL tenv) t0' disc p1 p2 = Some v'->
  fromVal (RVal v) = v'.

Ltac destruct_ilexpr := repeat (match goal with
                                  | [x : match ?X : option ILExpr with _ => _ end = _ |- _] =>
                                    let newH := fresh "H" in destruct X eqn: newH; tryfalse
                                end).

Hint Rewrite Z2Nat.inj_add Nat2Z.id Nat2Z.inj_add : ILDB.
Hint Resolve Zle_0_nat.

Lemma delay_trace_at d t : delay_trace d t d = t O.
Proof.
  unfold delay_trace. 
  assert (Compare_dec.leb d d = true) as E by (apply leb_correct; auto).
  rewrite E. rewrite minus_diag. reflexivity.
Qed.

Lemma plus0_0_n : forall n : nat,
  plus0 0 n = n.
Proof.
  intros.
  destruct n as [| n']; reflexivity.
Qed.

Lemma fromVal_RVal_eq v : fromVal (RVal v) = ILRVal v.
Proof. reflexivity. Qed.

Lemma fold_unfold_ILTexprSem t t0 tenv:
  ILTexprSem (match t with
               | Tvar _ => ILTplus (ILTexpr t) t0
               | Tnum 0 => t0
               | Tnum (S _) => ILTplus (ILTexpr t) t0
              end) tenv = ILTexprSem (tsmartPlus (ILTexpr t) t0) tenv.
Proof.
  reflexivity.
Qed.

Theorem Contr_translation_sound: forall c envC extC t0 t0',
  translation_sound c envC extC t0 t0'.
Proof.
  intro c. induction c;  unfold translation_sound.
 Focus 5.
  + (*Translate *)
    intros. simpl in *.
    option_inv_auto. rewrite adv_ext_iter in H3. rewrite delay_trace_iter.
    eapply IHc with (envC := envC); try eassumption. simpl.
    rewrite Nat2Z.inj_add. rewrite fold_unfold_ILTexprSem. rewrite tsmartPlus_sound. simpl.
    rewrite Nat2Z.inj_add. rewrite Nat2Z.inj_add in H3.
    rewrite Zplus_comm in H3. rewrite Zplus_assoc in H3. rewrite H3.
    reflexivity. simpl. rewrite fold_unfold_ILTexprSem. rewrite tsmartPlus_sound. simpl.
    (*replace (TexprSem t tenv + ILTexprSem t0 tenv + t0') with (ILTexprSem t0 tenv + t0' + TexprSem t tenv) at 1.*)
    rewrite <- plus_assoc. rewrite <- sum_delay. destruct (horizon c tenv) eqn:Hhor.
    - simpl. eapply sum_list_zero_horizon with (c:=c) (tenv:=tenv). assumption.
      erewrite zero_horizon_delay_trace. eassumption. eassumption. eassumption.
    - unfold plus0. reflexivity.
  + (* Zero *)
    intros. simpl in *. some_inv. subst. simpl in *. some_inv. compute. unfold compose in H2. some_inv.
    reflexivity.
  + (* Let *)
    intros. tryfalse.
  + (* Transfer *)
    intros. simpl in *. some_inv. subst. rewrite Rplus_0_r. unfold compose in H2. some_inv.
    rewrite delay_trace_at. unfold singleton_trace, singleton_trans.
    destruct (Party.eqb p p0).
    - simpl in *. some_inv. subst. rewrite Rmult_0_r. destruct t0; reflexivity. 
    - simpl in *. some_inv. unfold eval_payoff. destruct (Party.eqb p p1); destruct (Party.eqb p0 p2);
      try (rewrite H; rewrite Rmult_1_r; reflexivity);
      simpl; destruct (Party.eqb p p2); destruct (Party.eqb p0 p1); simpl; try (rewrite H); apply f_equal;
       try (rewrite plus_comm); try ring; try assumption; reflexivity.
  + (* Scale *)
    intros. simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
    destruct_vals. some_inv. subst. rewrite <- delay_scale_trace. unfold scale_trace, compose, scale_trans.
    rewrite summ_list_common_factor. rewrite <- fromVal_RVal_eq. apply fromVal_RVal_f_eq.
    - eapply Exp_translation_sound; try (simpl in *; some_inv; subst); try eassumption. simpl. rewrite <- Nat2Z.inj_add. eassumption.
    - eapply IHc with (envC := envC) (curr := curr); try eassumption. autounfold in *. simpl.
      rewrite H3. reflexivity. reflexivity.
  + (* Both *)
    intros. simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto. destruct_vals. some_inv.
    rewrite <- delay_add_trace. unfold add_trace, add_trans. rewrite summ_list_plus. rewrite <- fromVal_RVal_eq.
    apply fromVal_RVal_f_eq.
    - eapply IHc1 with (envC:=envC); try eassumption. autounfold in *. simpl. rewrite H2. reflexivity.
      destruct (Max.max_dec (horizon c1 tenv) (horizon c2 tenv)) as [Hmax_h1 | Hmax_h2].
      * rewrite Hmax_h1. reflexivity.
      * rewrite Hmax_h2. apply NPeano.Nat.max_r_iff in Hmax_h2.
        assert (Hh2eq: horizon c2 tenv = horizon c1 tenv + (horizon c2 tenv - horizon c1 tenv)). omega.
        rewrite Hh2eq. erewrite sum_before_after_horizon. reflexivity. eassumption.
    - eapply IHc2 with (envC:=envC); try eassumption. autounfold in *. simpl. rewrite H3. reflexivity.
      destruct (Max.max_dec (horizon c1 tenv) (horizon c2 tenv)) as [Hmax_h1 | Hmax_h2].
      * rewrite Hmax_h1. apply NPeano.Nat.max_l_iff in Hmax_h1.
        assert (Hh2eq: horizon c1 tenv = horizon c2 tenv + (horizon c1 tenv - horizon c2 tenv)). omega.
        rewrite Hh2eq. erewrite sum_before_after_horizon. reflexivity. eassumption.
      * rewrite Hmax_h2. reflexivity.
  + (* If *)
    intros. simpl in *. option_inv_auto. simpl in *. unfold loop_if_sem in H5.
    generalize dependent t0. generalize dependent v'.
    generalize dependent e. generalize dependent x.
    generalize dependent t0'.
    remember (TexprSem t tenv) eqn:Ht.
    revert t Ht.
    induction n.
    - (* n = 0 *)
      intros.
      simpl in *. destruct (fromExp (ILTexprZ t0) e) eqn:Hfromexp; tryfalse.
      option_inv_auto. simpl in *. subst.
      destruct (E[|e|] envC (adv_ext (Z.of_nat (ILTexprSem t0 tenv + t0')) extC)) eqn: Hexp; tryfalse.
      destruct v; tryfalse. destruct b.
      * (* Condition evaluates to true *)      
        replace x3 with (fromVal (BVal true)) in H8. simpl in H8.
        eapply IHc1 with (envC:=envC); try eassumption. simpl. rewrite H6.
        reflexivity. rewrite plus0_0_n.
        destruct (Max.max_dec (horizon c1 tenv) (horizon c2 tenv)) as [Hmax_h1 | Hmax_h2].
        rewrite Hmax_h1. reflexivity.
        rewrite Hmax_h2. apply NPeano.Nat.max_r_iff in Hmax_h2.
        assert (Hh2eq: horizon c2 tenv = horizon c1 tenv + (horizon c2 tenv - horizon c1 tenv)). omega.
        rewrite Hh2eq. erewrite sum_before_after_horizon. reflexivity. eassumption.
        eapply Exp_translation_sound; rewrite Nat2Z.inj_add in Hexp; try eassumption.
     * (* Condition evaluates to false *)
       replace x3 with (fromVal (BVal false)) in H8. simpl in H8.
       eapply IHc2 with (envC:=envC); try eassumption. simpl. rewrite H6.
       reflexivity. rewrite plus0_0_n.
       destruct (Max.max_dec (horizon c1 tenv) (horizon c2 tenv)) as [Hmax_h1 | Hmax_h2].
       rewrite Hmax_h1. apply NPeano.Nat.max_l_iff in Hmax_h1.
       assert (Hh2eq: horizon c1 tenv = horizon c2 tenv+ (horizon c1 tenv - horizon c2 tenv)). omega.
       rewrite Hh2eq. simpl. simpl. erewrite sum_before_after_horizon. reflexivity. eassumption.
       rewrite Hmax_h2. simpl. simpl. reflexivity.
       eapply Exp_translation_sound; rewrite Nat2Z.inj_add in Hexp; try eassumption.
    - (* n = S n' *) 
      intros. simpl in *. option_inv_auto.      
      destruct (E[|e|] envC (adv_ext (Z.of_nat (ILTexprSem t0 tenv + t0')) extC)) eqn: Hexp; tryfalse.
      destruct v; tryfalse. destruct b.
      * (* Condition evaluates to true *)      
        replace x3 with (fromVal (BVal true)) in H8. simpl in H8.
        eapply IHc1 with (envC:=envC) (tenv:=tenv); try eassumption. simpl. rewrite H6. reflexivity.
        destruct (Max.max_dec (horizon c1 tenv) (horizon c2 tenv)) as [Hmax_h1 | Hmax_h2].
        (* max = horizon c1 *)
        rewrite Hmax_h1. destruct (horizon c1 tenv) eqn:Hhor1. reflexivity.
        unfold plus0. rewrite <- Hhor1. replace (S n + horizon c1 tenv) with (horizon c1 tenv + S n).
        erewrite sum_before_after_horizon; try reflexivity; try eassumption. ring.
        (* max = horizon c2 *)
        rewrite Hmax_h2. apply NPeano.Nat.max_r_iff in Hmax_h2.
        destruct (horizon c2 tenv) eqn:Hhor2.
        simpl. eapply sum_list_zero_horizon with (c:=c1) (tenv:=tenv).
        omega. erewrite zero_horizon_delay_trace with (c:=c1) (tenv:=tenv). eassumption. omega. eassumption.
        
        unfold plus0. rewrite <- Hhor2.
        assert (Hh2eq: S n + horizon c2 tenv = horizon c1 tenv + ((horizon c2 tenv - horizon c1 tenv)) + S n). omega.
        rewrite Hh2eq. rewrite <- plus_assoc.
        erewrite sum_before_after_horizon. reflexivity. eassumption.
        
        eapply Exp_translation_sound with (envC:=envC) (envT:=tenv);
        rewrite Nat2Z.inj_add in Hexp; autounfold; try eassumption.
     * (* Condition evaluates to false *)
       destruct (max (horizon c1 tenv) (horizon c2 tenv)) eqn:Hmax. simpl in *.
       Focus 2.
       unfold plus0 in *. rewrite <- Hmax. rewrite <- Hmax in IHn.
       destruct (Max.max_dec (horizon c1 tenv) (horizon c2 tenv)) as [Hmax_h1 | Hmax_h2]. simpl.
       (* max = horizon c1 *)
       rewrite Hmax_h1. rewrite Hmax_h1 in IHn.
       (*destruct (E[|e|] envC (adv_ext (Z.of_nat (ILTexprSem t0 tenv + t0')) extC)) eqn: Hexp; tryfalse.*)
       replace x3 with (fromVal (BVal false)) in H8. simpl in H8. rewrite adv_ext_iter in H6.
       
       option_inv_auto. rewrite delay_trace_at. rewrite delay_trace_empty_before_n.
       unfold empty_trans. rewrite Rmult_0_r. rewrite Rplus_0_l.
       rewrite delay_trace_iter. simpl. rewrite plus_n_Sm.
       eapply IHn with (t:=Tnum n); try eassumption. reflexivity. rewrite <- plus_n_Sm.
       replace (Z.of_nat (S (ILTexprSem t0 tenv + t0'))) with (Z.of_nat (ILTexprSem t0 tenv + t0') + 1)%Z.
       apply H4. rewrite <- of_nat_succ. apply f_equal. omega. omega.
       eapply Exp_translation_sound; try eassumption. rewrite Nat2Z.inj_add in Hexp; eassumption.

       (* max = horizon c2 *)
       rewrite Hmax_h2. rewrite Hmax_h2 in IHn. simpl.
       replace x3 with (fromVal (BVal false)) in H8. simpl in H8. rewrite adv_ext_iter in H6.
       option_inv_auto. rewrite delay_trace_at. rewrite delay_trace_empty_before_n.
       unfold empty_trans. rewrite Rmult_0_r. rewrite Rplus_0_l.
       rewrite delay_trace_iter. simpl. rewrite plus_n_Sm.
       eapply IHn with (t:=Tnum n); try eassumption. reflexivity.
       replace (Z.of_nat (ILTexprSem t0 tenv + S t0')) with (Z.of_nat (ILTexprSem t0 tenv + t0') + 1)%Z.
       apply H4. rewrite <- of_nat_succ. apply f_equal. omega. omega.
       eapply Exp_translation_sound; try eassumption. rewrite Nat2Z.inj_add in Hexp; eassumption.

       (* max = 0*)       
       replace x3 with (fromVal (BVal false)) in H8. simpl in H8. rewrite adv_ext_iter in H6.
       option_inv_auto. eapply IHn with (t:=Tnum n); try eassumption; try reflexivity.
       replace (Z.of_nat (ILTexprSem t0 tenv + S t0')) with (Z.of_nat (ILTexprSem t0 tenv + t0') + 1)%Z.
       apply H4. rewrite <- of_nat_succ. apply f_equal. ring.
       eapply Exp_translation_sound; try eassumption. rewrite Nat2Z.inj_add in Hexp; eassumption.
Qed.

Fixpoint cutPayoff (e : ILExpr) : ILExpr :=
  match e with
    | ILIf b e1 e2 => ILIf b (cutPayoff e1) (cutPayoff e2)
    | Model s t' => Model s t'
    | ILUnExpr op e1 => ILUnExpr op (cutPayoff e1)
    | ILBinExpr op e1 e2 => ILBinExpr op (cutPayoff e1) (cutPayoff e2)
    | ILLoopIf cond e1 e2 t => ILLoopIf cond (cutPayoff e1) (cutPayoff e2) t
    | FloatV v => FloatV v
    | NatV v => NatV v
    | ILtexpr t => ILtexpr t
    | ILtvar v => ILtvar v
    | Payoff t' p1 p2 => ILIf (ILBinExpr ILLessN (ILtexpr t') (ILtvar (Tv 0))) (FloatV 0%R) (Payoff t' p1 p2)
  end.

(*Semantic equvivalence of IL expressions*)

Definition ILequiv tenv e1 e2 := forall ext t0 disc p1 p2, IL[|e1|] ext tenv t0 disc p1 p2 = IL[|e2|]ext tenv t0 disc p1 p2.

Notation "e1 '~~[' tenv ']' e2" := (ILequiv tenv e1 e2) (at level 50).

(* We treat variable (Tv 0) as "current time" *)
Definition set_t_now tenv t_now := tenv_update tenv (Tv 0) t_now.

Lemma cutPayoff_eq_compiled_expr e e_il t0: fromExp t0 e = Some e_il -> e_il = cutPayoff e_il.
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
    eapply all_to_forall3 in H; inversion_clear H as [IHe1 IHe']; inversion_clear IHe' as [IHe2 IHe3];
    option_inv_auto; subst; simpl in *; try some_inv; subst.
    simpl in *. erewrite <- IHe2;eauto. erewrite <- IHe3;eauto.
  - simpl in *. some_inv. reflexivity.
Qed.

Import NPeano.

Lemma ltb_plus_l_false n1 n2 n3:
  ltb n1 n2 = false ->
  ltb (n3 + n1) n2 = false.
Proof.
  intros. apply not_true_is_false. apply not_true_iff_false in H. unfold not in *. intros. apply ltb_lt in H0.
  apply H. apply ltb_lt.  omega.
Qed.

Lemma ltb_plus_both_false n1 n2 n3:
  ltb n1 n2 = false -> ltb (n3 + n1) (n3 + n2) = false.
Proof.
  intros. apply not_true_is_false. apply not_true_iff_false in H. unfold not in *. intros. apply ltb_lt in H0.
  apply H. apply ltb_lt.  omega.
Qed.
  
Lemma ILexpr_eq_cutPayoff_at_zero e tenv: e ~~[tenv_update tenv (Tv 0) 0] cutPayoff e.
Proof.
  generalize dependent tenv.
  induction e; intros; simpl in *; unfold ILequiv; try reflexivity.
  - intros. simpl. unfold bind,compose,pure.
    remember (IL[|e1|] ext (tenv_update tenv (Tv 0) 0) t0 disc p1 p2) as ILv1.
    destruct ILv1; tryfalse; try reflexivity. destruct i; try reflexivity. destruct b. apply IHe2. apply IHe3.
  - intros. simpl. unfold bind,compose,pure. rewrite IHe. reflexivity.
  - intros. simpl. unfold bind,compose,pure. rewrite IHe1. rewrite IHe2. reflexivity.
  - intros. simpl.
    generalize dependent t0.
    induction (TexprSem t (tenv_update tenv (Tv 0) 0)).
    + intros; simpl. rewrite IHe1. rewrite IHe2. rewrite IHe3. reflexivity.
    + intros; simpl. unfold bind,compose,pure. rewrite IHe1. rewrite IHe2.
      destruct (IL[|cutPayoff e1|] ext (tenv_update tenv (Tv 0) 0) t0 disc p1 p2); try reflexivity. destruct i; try reflexivity.
      destruct b; try reflexivity. apply IHn.
Qed.

Hint Resolve cutPayoff_eq_compiled_expr.

Require Import Arith.Compare_dec. 
Lemma ILexpr_eq_cutPayoff_at_n e tenv c t0 n t_now:
  fromContr c t0 = Some e ->
  ILTexprSem t0 (tenv_update tenv (Tv 0) t_now) = n ->
  NPeano.ltb n t_now = false ->
  e ~~[tenv_update tenv (Tv 0) t_now] cutPayoff e.
Proof.
  intros. generalize dependent e. generalize dependent t0. generalize dependent n.
  induction c; intros; simpl in *; tryfalse; some_inv; subst; unfold ILequiv; intros.
  - reflexivity.
  - simpl in *. some_inv. unfold eval_payoff. destruct (Party.eqb p p0); simpl; try reflexivity. unfold tenv_update at 3.
    simpl. rewrite ltb_plus_l_false; eauto.
  - option_inv_auto. some_inv. subst. simpl. unfold bind,compose,pure.
    replace (cutPayoff x) with x by eauto. rewrite <- IHc with (n:=(ILTexprSem t0 (tenv_update tenv (Tv 0) t_now))) (t0:=t0). reflexivity.
    assumption. reflexivity. assumption.
  - unfold ILequiv in IHc.
    replace match t with
        | Tvar _ => ILTplus (ILTexpr t) t0
        | Tnum 0 => t0
        | Tnum (S _) => ILTplus (ILTexpr t) t0
                         end with (tsmartPlus (ILTexpr t) t0) in H by reflexivity.
    eapply IHc with (t0:=(tsmartPlus (ILTexpr t) t0)) (n:=ILTexprSem (tsmartPlus (ILTexpr t) t0) (tenv_update tenv (Tv 0) t_now)).
    simpl. rewrite fold_unfold_ILTexprSem. rewrite tsmartPlus_sound. simpl. apply not_true_is_false. unfold not. intros.
    apply NPeano.ltb_lt in H0. apply not_true_iff_false in H1. unfold not in H1. rewrite NPeano.ltb_lt in H1. apply H1. omega. reflexivity.
    assumption.
  - option_inv_auto. some_inv. subst. simpl. unfold bind,compose,pure. erewrite <- IHc1; eauto. erewrite <- IHc2; eauto.
  - option_inv_auto. some_inv. subst. simpl. unfold bind,compose,pure.
    generalize dependent t1.
    induction (TexprSem t (tenv_update tenv (Tv 0) t_now)); intros.
    + simpl. unfold bind,compose,pure. erewrite <- IHc1; eauto. erewrite <- IHc2; eauto.
    + simpl. unfold bind,compose,pure. erewrite <- IHc1; eauto. simpl in *.
      destruct (IL[|x1|] ext (tenv_update tenv (Tv 0) t_now) t1 disc p1 p2); try reflexivity.
      destruct i; try reflexivity. destruct b.
      * reflexivity.
      * simpl. rewrite IHn. reflexivity.
Qed.

Lemma horizon_smartScale_eq c e' tenv:
  isZeroLit e' = false ->
  horizon c tenv = horizon (smartScale e' c) tenv.
Proof.
  intros. unfold smartScale. rewrite H. destruct c; reflexivity.
Qed.
  
Lemma horizon_gt_0_smartScale c e' tenv:
  0 < horizon (smartScale e' c) tenv ->
  horizon c tenv = horizon (smartScale e' c) tenv.
Proof.
  generalize dependent e'.
  induction c; intros; simpl; unfold smartScale;
  try (destruct (isZeroLit e') eqn:HisZ; unfold smartScale in H; try (rewrite HisZ in *); simpl in *; inversion H; reflexivity).
Qed.

(*Lemma exp_not_zero_smartScale c e' tenv:
  0 < horizon (smartScale e' c) tenv ->
  horizon c tenv = horizon (smartScale e' c) tenv.
Proof.
  generalize dependent e'.
  induction c; intros; simpl; unfold smartScale;
  try (destruct (isZeroLit e') eqn:HisZ; unfold smartScale in H; try (rewrite HisZ in ; simpl in *; inversion H; reflexivity).
Qed.*)
       
Lemma horizon_eq_0_smartScale c e' tenv:
  horizon c tenv = 0->
  horizon (smartScale e' c) tenv = 0.
Proof.
  generalize dependent e'.
  induction c; intros; simpl in *; unfold smartScale; destruct (isZeroLit e') eqn:HisZ; tryfalse; simpl; try reflexivity; auto.
Qed.

Hint Resolve ext_inst_typed env_inst_typed.

Hint Constructors Red.

Lemma horizon_smartBoth c1 c2 tenv:
  horizon (Both c1 c2) tenv = horizon (smartBoth c1 c2) tenv.
Proof.
  simpl. destruct c1; simpl; try reflexivity; destruct c2; try (rewrite Max.max_0_r); try reflexivity.
Qed. 

Check within_sem.

(*
Lemma within_sem_specialiseExp: forall c1 c2 e n env ext extC envC g,
  TypeExt extC ->
  TypeEnv g envC ->
  g |-E e ∶ BOOL ->
  ext_inst ext extC ->
  env_inst env envC ->
  within_sem c1 c2 e n envC extC = within_sem c1 c2 (specialiseExp e env ext) n envC extC.
Proof.
  induction n.
  - intros. simpl. apply functional_extensionality; intro. erewrite specialiseExp_sound; eauto.
  - intros. simpl. apply functional_extensionality; intro. erewrite specialiseExp_sound; eauto.
    erewrite IHn; eauto.
    rewrite ext_inst_adv. reflexivity.
 *)

(* loop_if_sem n 1
     (fun t : nat => IL[|x1|] extIL (set_t_now tenv 1) t disc p1 p2)
     (fun t : nat => IL[|x|] extIL (set_t_now tenv 1) t disc p1 p2)
     (fun t : nat => IL[|x0|] extIL (set_t_now tenv 1) t disc p1 p2) =
   loop_if_sem n 1
     (fun t : nat => IL[|x1|] extIL (set_t_now tenv 1) t disc p1 p2)
     (fun t : nat => IL[|cutPayoff x|] extIL (set_t_now tenv 1) t disc p1 p2)
     (fun t : nat => IL[|cutPayoff x0|] extIL (set_t_now tenv 1) t disc p1 p2)
*)

Lemma cutPayoff_ILsem_at_n : forall tenv m e n extIL disc p1 p2,
  m <= n ->
  IL[|cutPayoff e|] extIL (set_t_now tenv m) n disc p1 p2 = IL[|e|] extIL (set_t_now tenv m) n disc p1 p2.
Proof.
  induction e; simpl; auto.
  - intros; unfold liftM,compose,bind,pure. rewrite <- IHe1; auto. rewrite <- IHe2; auto. rewrite <- IHe3; auto.
  - induction (TexprSem t (set_t_now tenv m)).
    + intros; simpl. rewrite <- IHe1; auto. rewrite <- IHe2; auto. rewrite <- IHe3; auto.
    + intros; simpl. rewrite <- IHe1; auto. rewrite <- IHe2. rewrite IHn; auto. auto.
  - intros. rewrite plus_comm. rewrite ltb_plus_l_false. reflexivity. apply not_true_is_false. unfold not. intros.
    apply ltb_lt in H0. unfold set_t_now,tenv_update in *. simpl in *. omega.
Qed.

Lemma cutPayoff_ILsem_at_n' : forall nn tenv m e1 e2 cond n extIL disc p1 p2,
  m <= S n ->
  IL[|cond|] extIL (set_t_now tenv m) n disc p1 p2 = Some (ILBVal false) ->
  IL[|cutPayoff (ILLoopIf cond e1 e2 (Tnum (S nn)))|] extIL (set_t_now tenv m) n disc p1 p2 =
  IL[|ILLoopIf cond e1 e2 (Tnum (S nn))|] extIL (set_t_now tenv m) n disc p1 p2.
Proof.
  intros. simpl. unfold liftM,compose,bind,pure. rewrite H0.
  generalize dependent m. generalize dependent e1. generalize dependent e2. generalize dependent cond.
  generalize dependent n.
  - induction nn.
    + intros; simpl. unfold liftM,compose,bind,pure. rewrite cutPayoff_ILsem_at_n;eauto. rewrite cutPayoff_ILsem_at_n;eauto.
    + intros; simpl. unfold liftM,compose,bind,pure. cases (IL[|cond|] extIL (set_t_now tenv m) (S n) disc p1 p2); try reflexivity.
      cases i; try reflexivity. cases b.
      * rewrite cutPayoff_ILsem_at_n; eauto.
      * rewrite IHnn; eauto.
Qed.

Theorem cutPayoff_sound_one_step c c' envC extC:
  forall (il_e : ILExpr) (extIL : ExtEnv' ILVal) (envP : EnvP) (extP : ExtEnvP)
         (v' : ILVal) p1 p2 curr v trace (disc : nat -> R ) tenv tr g,
  (forall a a', Asset.eqb a a' = true) ->
  (forall l t, fromVal (extC l t) = extIL l t) ->
  fromContr c (ILTexpr (Tnum 0)) = Some il_e ->
  Red c envP extP c' tr ->
  (*C[|c|] envC extC (set_t_now tenv 1) = Some old_trace ->*)
  C[|c'|] envC (adv_ext 1 extC) (set_t_now tenv 1) = Some trace ->
  sum_list (map (fun t => (disc (1+t)%nat * trace t p1 p2 curr)%R)
                (seq 0 (horizon c' (set_t_now tenv 1)))) = v ->
  IL[|cutPayoff il_e|] extIL (set_t_now tenv 1) 0 disc p1 p2 = Some v'->
  TypeExt extC ->
  TypeEnv g envC ->
  g |-C c ->
  ext_inst extP extC ->
  env_inst envP envC ->
  fromVal (RVal v) = v'.
Proof.
  intros until g. intros A Xeq TC R Cs S ILs Tx Te T J I.
  generalize dependent il_e. generalize dependent extIL.
  generalize dependent trace. (*generalize dependent old_trace.*) generalize dependent disc.
  generalize dependent tenv. generalize dependent v. generalize dependent v'.
  induction R.
  Focus 10.
  - (* red_if0_true *)
    intros. inversion T.
    simpl in *. option_inv_auto. simpl in *. option_inv_auto.
    destruct (TexprSem n (set_t_now tenv 1)).
    + unfold loop_if_sem in *. option_inv_auto. simpl in *.
      unfold fromBLit in H.
      cases (specialiseExp b env ext); tryfalse. cases op; tryfalse. destruct args; tryfalse. some_inv. subst.
      replace x2 with (fromVal (BVal true)) in H5. simpl in H5.
      eapply IHR; eauto. eapply Exp_translation_sound with (envC:=envC) (extC:=extC); try eassumption. simpl. rewrite adv_ext_0.
      erewrite <- specialiseExp_sound with (envp:=env) (extp:=ext) (ext:=extC); eauto. erewrite Eq. simpl. reflexivity.
    + unfold loop_if_sem in *. option_inv_auto. simpl in *.
      unfold fromBLit in H.
      cases (specialiseExp b env ext); tryfalse. cases op; tryfalse. destruct args; tryfalse. some_inv. subst.
      replace x2 with (fromVal (BVal true)) in H5. simpl in H5.
      eapply IHR; eauto. eapply Exp_translation_sound with (envC:=envC) (extC:=extC); try eassumption. simpl. rewrite adv_ext_0.
      erewrite <- specialiseExp_sound with (envp:=env) (extp:=ext) (ext:=extC); eauto. erewrite Eq. simpl. reflexivity.
  - (* red_zero *)intros. simpl in *. some_inv. subst. simpl in *. unfold compose,bind,pure in *. some_inv. reflexivity.
  - (* red_let *)
    intros. simpl in *.
    option_inv_auto.
  - (* red_transf *)
    intros. simpl in *. option_inv_auto. simpl in *. some_inv. subst.
    destruct (Party.eqb c p0).
    + simpl in *. some_inv. reflexivity.
    + simpl in *. some_inv. reflexivity.
  - (* red_scale *)
    intros. subst. simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
    destruct_vals. some_inv. subst.
    inversion T. unfold smartScale in Cs.
    cases (isZeroLit (TranslateExp.translateExp (-1) (specialiseExp e env ext))) as Zerolit.

    + simpl in *. some_inv. rewrite sum_of_map_empty_trace.
      assert (E[|TranslateExp.translateExp (-1) (specialiseExp e env ext)|] envC (adv_ext 1 extC) = Some (RVal 0)) as Hexp.
      rewrite isZeroLit_true with (x:=TranslateExp.translateExp (-1) (specialiseExp e env ext)). reflexivity. eassumption.      
      symmetry. apply ILRVal_zero_mult_l. symmetry.
      erewrite <- cutPayoff_eq_compiled_expr in H2. try eassumption.
      
      rewrite TranslateExp.translateExp_ext in Hexp.
      erewrite specialiseExp_sound in Hexp; try (rewrite adv_ext_iter; simpl; rewrite adv_ext_0); try assumption.
      rewrite <- fromVal_RVal_eq.
      eapply Exp_translation_sound with (envC:=envC);
      try (simpl in *; some_inv; subst); try eassumption. simpl.
      rewrite adv_ext_iter in Hexp. simpl in *. eassumption.
      eassumption. assumption. eassumption. reflexivity.
    + erewrite <- cutPayoff_eq_compiled_expr in H2; try eassumption.
      replace (match c' with
                 | Zero => Zero
                 | _ => Scale (TranslateExp.translateExp (-1) (specialiseExp e env ext)) c'
               end) with (smartScale (TranslateExp.translateExp (-1) (specialiseExp e env ext)) c') in Cs.
      erewrite smartScale_sound in Cs; eauto.
      simpl in *. option_inv_auto. some_inv. subst. simpl in *. option_inv_auto.
      destruct_vals. some_inv. subst. unfold scale_trace, compose, scale_trans.
      rewrite summ_list_common_factor. rewrite <- fromVal_RVal_eq. apply fromVal_RVal_f_eq.
      * eapply Exp_translation_sound; try (simpl in *; some_inv; subst); try eassumption. simpl.
        rewrite TranslateExp.translateExp_ext in H4.
        erewrite specialiseExp_sound in H4; eauto; try (rewrite adv_ext_iter in H4; simpl; rewrite adv_ext_0 in H4);
        try (rewrite adv_ext_iter; simpl; rewrite adv_ext_0); eauto.
      * eapply IHR; eauto. rewrite <- horizon_smartScale_eq. reflexivity. assumption.
      * constructor. apply TranslateExp.translateExp_type; eauto. eapply Preservation.red_typed; eauto.
      * unfold smartScale. rewrite Zerolit. reflexivity.       
  - (*red_trans0 *)
    intros. inversion T. simpl in *. option_inv_auto. eapply IHR; eauto.
  - (*red_transS *)
    intros. inversion T. 
    subst. simpl in *. option_inv_auto.

    eapply Contr_translation_sound with (envC:=envC) (tenv:=set_t_now tenv 1); eauto; try reflexivity. simpl.
    unfold liftM,compose,bind,pure. erewrite adv_ext_iter in H0. instantiate (2:=0).

    replace (Z.pos (Pos.of_succ_nat (n + 0 + 0))) with (1 + Z.of_nat n)%Z. rewrite H0. reflexivity.
    rewrite Zpos_P_of_succ_nat. replace (n + 0 + 0) with n by omega. omega.
    simpl. replace (n + 0 + 0) with n by omega.
    rewrite <- NPeano.Nat.add_1_l. rewrite plus_comm. replace (n + 1) with (n +1 + 0) by omega.
    rewrite <- sum_delay.
    replace (n + 1 + horizon c (set_t_now tenv 1)) with (S (n + horizon c (set_t_now tenv 1))) by omega. simpl.
    erewrite Soundness.red_sound1 with (t:=empty_trans) (c:=Translate (Tnum (S n)) c); eauto.
    unfold empty_trans. rewrite Rmult_0_r. rewrite Rplus_0_l.
    destruct (horizon c (set_t_now tenv 1)) eqn:Hhor.
    + simpl. eapply sum_list_zero_horizon with (c:=c) (tenv:=set_t_now tenv 1). assumption.
      erewrite zero_horizon_delay_trace. eassumption. eassumption. eassumption.
    + unfold plus0. replace (n + 1 + 0) with (n + 1) by omega.
      rewrite plus_comm. replace 1 with (0 + 1) at 1 by reflexivity.
      rewrite sum_delay'. simpl.  reflexivity.
    + simpl. instantiate (1:=set_t_now tenv 1). unfold liftM,compose,bind,pure.
      replace (Z.pos (Pos.of_succ_nat n)) with (1 + Z.of_nat n)%Z. rewrite adv_ext_iter in H0. rewrite H0.
      replace (n + 1 + 0) with (S n) by omega. reflexivity.
      rewrite Zpos_P_of_succ_nat. replace (n + 0 + 0) with n by omega.
      omega.
    + rewrite <- ILs. eapply ILexpr_eq_cutPayoff_at_n; try eassumption. reflexivity. simpl.
      apply not_true_is_false. unfold not. intros. apply NPeano.ltb_lt in H. omega.
  - (*red_both *)
    intros. inversion T.
    simpl in *.  option_inv_auto. some_inv. subst. erewrite smartBoth_sound in Cs; eauto.
    simpl in *. option_inv_auto. destruct_vals. some_inv. rewrite <- horizon_smartBoth. simpl.
    unfold add_trace, add_trans. rewrite summ_list_plus. rewrite <- fromVal_RVal_eq.
    apply fromVal_RVal_f_eq.
    + eapply IHR1; try eassumption.
      destruct (Max.max_dec (horizon c1' (set_t_now tenv 1)) (horizon c2' (set_t_now tenv 1))) as [Hmax_h1 | Hmax_h2].
      * rewrite Hmax_h1. reflexivity.
      * rewrite Hmax_h2. apply NPeano.Nat.max_r_iff in Hmax_h2.
        assert (Hh2eq: horizon c2' (set_t_now tenv 1) =
                       (horizon c1' (set_t_now tenv 1)) + (horizon c2' (set_t_now tenv 1) - horizon c1' (set_t_now tenv 1))). omega.
        rewrite Hh2eq. replace x1 with (delay_trace 0 x1) by apply delay_trace_0.
        erewrite sum_before_after_horizon. reflexivity. eassumption.
    + eapply IHR2; try eassumption.
      destruct (Max.max_dec (horizon c1' (set_t_now tenv 1)) (horizon c2' (set_t_now tenv 1))) as [Hmax_h1 | Hmax_h2].
      * rewrite Hmax_h1. apply NPeano.Nat.max_l_iff in Hmax_h1.
        assert (Hh2eq: (horizon c1' (set_t_now tenv 1)) =
                       (horizon c2' (set_t_now tenv 1)) + ((horizon c1' (set_t_now tenv 1)) - (horizon c2' (set_t_now tenv 1)))). omega.
        rewrite Hh2eq. replace x2 with (delay_trace 0 x2) by apply delay_trace_0.
        erewrite sum_before_after_horizon. reflexivity. eassumption.
      * rewrite Hmax_h2. reflexivity.      
    + constructor. eapply Preservation.red_typed. eauto. eauto. apply H4. eassumption.
      eapply Preservation.red_typed. eauto. eauto. apply H5. eassumption.
  - (* red_if0_false *)
    intros. inversion T.
    simpl in *. option_inv_auto. simpl in *. option_inv_auto.
    unfold fromBLit in H.
    cases (specialiseExp b env ext); tryfalse. cases op; tryfalse. destruct args; tryfalse. some_inv. subst.
    replace x2 with (fromVal (BVal false)) in H5. simpl in H5.
    eapply IHR; eauto. eapply Exp_translation_sound with (envC:=envC) (extC:=extC); try eassumption. simpl. rewrite adv_ext_0.
    erewrite <- specialiseExp_sound with (envp:=env) (extp:=ext) (ext:=extC); eauto. erewrite Eq. simpl. reflexivity.
  - (* red_ifS_false *)
    intros. inversion T.
    eapply Contr_translation_sound with (t0':=O) (envC := envC) (tenv:=(set_t_now tenv 1)); eauto. simpl.
    simpl in *. option_inv_auto. simpl in *. option_inv_auto. unfold liftM,compose,bind,pure.
    erewrite <- specialiseExp_sound; eauto.
    rewrite Esem_fromBLit with (r:=false); eauto. rewrite adv_ext_0.
    rewrite Cs. reflexivity.

    simpl. rewrite delay_trace_0. rewrite <- S. subst. simpl.
    cases (max (horizon c1 (set_t_now tenv 1)) (horizon c2 (set_t_now tenv 1))) as Hmax.
    + reflexivity.
    + unfold plus0. rewrite <- Hmax.
      destruct (Max.max_dec (horizon c1 (set_t_now tenv 1)) (horizon c2 (set_t_now tenv 1))) as [Hmax_h1 | Hmax_h2].
      * rewrite Hmax_h1. simpl.
        erewrite Soundness.red_sound1 with (t:=empty_trans) (c:=If b (Tnum (S n)) c1 c2); eauto.
        unfold empty_trans. rewrite Rmult_0_r. rewrite Rplus_0_l. replace 1 with (0 + 1) at 1 by reflexivity.
        rewrite sum_delay'. simpl. rewrite delay_trace_0.  reflexivity. simpl. erewrite <- specialiseExp_sound; eauto.
        rewrite Esem_fromBLit with (r:=false); eauto. unfold liftM,compose,bind,pure. simpl in *.
        instantiate (1:= set_t_now tenv 1). rewrite Cs. reflexivity.
      * rewrite Hmax_h2. simpl.
        erewrite Soundness.red_sound1 with (t:=empty_trans) (c:=If b (Tnum (S n)) c1 c2); eauto.
        unfold empty_trans. rewrite Rmult_0_r. rewrite Rplus_0_l. replace 1 with (0 + 1) at 1 by reflexivity.
        rewrite sum_delay'. simpl. rewrite delay_trace_0.  reflexivity. simpl. erewrite <- specialiseExp_sound; eauto.
        rewrite Esem_fromBLit with (r:=false); eauto. unfold liftM,compose,bind,pure. simpl in *.
        instantiate (1:= set_t_now tenv 1). rewrite Cs. reflexivity.
    + intros. rewrite <- ILs. simpl in *. option_inv_auto. symmetry.      
      apply cutPayoff_ILsem_at_n'; eauto. simpl in *. option_inv_auto. simpl in *. option_inv_auto. simpl in *.
      assert (fromVal (BVal false) = x2).
      eapply Exp_translation_sound with (envC:=envC) (extC:=extC); try eassumption.
      erewrite <- specialiseExp_sound with (envp:=env) (extp:=ext) (ext:=extC); eauto.
      rewrite Esem_fromBLit with (r:=false); eauto. simpl in *. rewrite H0 in *. assumption.
Qed.
