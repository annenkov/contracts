Add LoadPath "..".

Require Import Tactics.
Require Import ILSyntax.
Require Import ILSemantics.
Require Import Denotational.
Require Import Syntax.
Require Import Utils.
Require Import Horizon.
Require Import Misc.

Require Import List.
Require Import ZArith.
Require Import FunctionalExtensionality.
Require Import Coq.Program.Equality.

Import ListNotations.

Local Open Scope Z.

Fixpoint fromExp (t0 : ILTExpr) (e : Exp) :=
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
    | Obs lab t => Some (Model lab (ILTplusZ t t0))
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
    | Scale e c      => fromExp t0 e
                                >>= fun v => (fromContr c t0)
                                               >>= fun v' => pure (ILBinExpr ILMult v v')                          
    | Translate t' c => fromContr c (ILTplus (ILTexpr t') t0)
    | If e t' c1 c2  => (fromContr c1 t0)
                          >>= fun v1 => (fromContr c2 t0)
                                          >>= fun v2 => fromExp t0 e
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
  E[|e|] envC (adv_ext (Z.of_nat (ILTexprSem t0 envT) + Z.of_nat t0') extC) = Some v ->
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
    replace (Z.of_nat t0' + (i + Z.of_nat (ILTexprSem t0 envT))) with (Z.of_nat (ILTexprSem t0 envT) + Z.of_nat t0' + i). eapply H0. ring.
  + (* Var *)
    intros. inversion H.
  + (* Acc *)
    intros. inversion H.
Qed.

Lemma delay_scale_trace tr t n :
  scale_trace n (delay_trace t tr) = delay_trace t (scale_trace n tr).
Proof.
  unfold scale_trace, delay_trace, compose. apply functional_extensionality. intros. destruct (leb t x).
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

Lemma sum_of_map_empty_trace : forall n n0 p1 p2 curr trace ,
  trace = empty_trace ->
  sum_list (map (fun t => trace t p1 p2 curr) (seq n0 n)) = 0%R.
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
  sum_list (map (fun t => (f t * (delay_trace (n + t0) tr) t p1 p2 curr)%R) (seq (t0+n) t)).
Proof.
  rewrite seq_split. rewrite map_app. rewrite sum_split. rewrite delay_trace_zero_before_n. rewrite Rplus_0_l. reflexivity.
Qed.

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
  intros. apply functional_extensionality. intros. unfold delay_trace. destruct (leb m x).
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
  unfold add_trace, delay_trace, compose. apply functional_extensionality. intros. destruct (leb n x).
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
  assert (leb d d = true) as E by (apply leb_correct; auto).
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

Theorem Contr_translation_sound: forall c envC extC t0 t0',
  translation_sound c envC extC t0 t0'.
Proof.
  intro c. induction c;  unfold translation_sound.
 Focus 5.
  + (*Translate *)
    intros. simpl in *.
    option_inv_auto. rewrite adv_ext_iter in H3. rewrite delay_trace_iter.
    eapply IHc with (envC := envC); try eassumption. simpl.
    rewrite Nat2Z.inj_add. rewrite Nat2Z.inj_add. rewrite Nat2Z.inj_add in H3.
    rewrite Zplus_comm in H3. rewrite Zplus_assoc in H3. rewrite H3.
    reflexivity. simpl.
    replace (TexprSem t tenv + ILTexprSem t0 tenv + t0') with (ILTexprSem t0 tenv + t0' + TexprSem t tenv) at 1.
    autorewrite with ILDB.
    (*replace (TexprSem t tenv + Z.to_nat (ILTexprSem0 0 t0 tenv) + t0') with (Z.to_nat (ILTexprSem0 0 t0 tenv) + t0' + TexprSem t tenv).
    reflexivity. omega. omega. assumption. rewrite Hseq.*)
    rewrite <- plus_assoc.
    rewrite <- sum_delay. destruct (horizon c tenv) eqn:Hhor.
    - simpl. eapply sum_list_zero_horizon with (c:=c) (tenv:=tenv). assumption.
      erewrite zero_horizon_delay_trace. eassumption. eassumption. eassumption.
    - unfold plus0. reflexivity.
    - omega.
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
    - eapply Exp_translation_sound; try (simpl in *; some_inv; subst); try eassumption. rewrite  <- Nat2Z.inj_add. eassumption.
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
      simpl in *. destruct (fromExp t0 e) eqn:Hfromexp; tryfalse.
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
       destruct (within_sem C[|c1|] C[|c2|] e n envC (adv_ext (Z.of_nat (ILTexprSem t0 tenv + t0') + 1) extC) tenv) eqn:Hwithin; tryfalse.
       option_inv_auto. rewrite delay_trace_at. rewrite delay_trace_empty_before_n.
       unfold empty_trans. rewrite Rmult_0_r. rewrite Rplus_0_l.
       rewrite delay_trace_iter. rewrite <- of_nat_succ in Hwithin. simpl. rewrite plus_n_Sm.
       eapply IHn with (t:=Tnum n); try eassumption. reflexivity. rewrite <- plus_n_Sm. eapply Hwithin. omega. 
       eapply Exp_translation_sound; try eassumption. rewrite Nat2Z.inj_add in Hexp; eassumption.

       (* max = horizon c2 *)
       rewrite Hmax_h2. rewrite Hmax_h2 in IHn. simpl.
       replace x3 with (fromVal (BVal false)) in H8. simpl in H8. rewrite adv_ext_iter in H6.
       destruct (within_sem C[|c1|] C[|c2|] e n envC (adv_ext (Z.of_nat (ILTexprSem t0 tenv + t0') + 1) extC) tenv) eqn:Hwithin; tryfalse.
       option_inv_auto. rewrite delay_trace_at. rewrite delay_trace_empty_before_n.
       unfold empty_trans. rewrite Rmult_0_r. rewrite Rplus_0_l.
       rewrite delay_trace_iter. rewrite <- of_nat_succ in Hwithin. simpl. rewrite plus_n_Sm.
       eapply IHn with (t:=Tnum n); try eassumption. reflexivity. rewrite <- plus_n_Sm. eapply Hwithin. omega. 
       eapply Exp_translation_sound; try eassumption. rewrite Nat2Z.inj_add in Hexp; eassumption.

       (* max = 0*)       
       replace x3 with (fromVal (BVal false)) in H8. simpl in H8. rewrite adv_ext_iter in H6.
       destruct (within_sem C[|c1|] C[|c2|] e n envC (adv_ext (Z.of_nat (ILTexprSem t0 tenv + t0') + 1) extC) tenv) eqn:Hwithin; tryfalse.
       rewrite <- of_nat_succ in Hwithin.
       eapply IHn with (t:=Tnum n); try eassumption; try reflexivity.
       rewrite <- plus_n_Sm. eapply Hwithin.
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
    | Payoff t' p1 p2 => ILIf (ILBinExpr ILLessN (ILtexpr t') (ILtexpr (ILTexpr (Tvar (Tv 0))))) (FloatV 0%R) (Payoff t' p1 p2)
  end.

(*Semantic equvivalence of IL expressions*)
Check ILsem.
Definition ILequiv tenv e1 e2 := forall ext t0 disc p1 p2, IL[|e1|] ext tenv t0 disc p1 p2 = IL[|e2|]ext tenv t0 disc p1 p2.

Notation "e1 '~~[' tenv ']' e2" := (ILequiv tenv e1 e2) (at level 50).

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
