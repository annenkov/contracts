Add LoadPath "..".

Require Import Tactics.
Require Import Denotational.
Require Import TranslateExp.
Require Import ILSyntax.
Require Import ILSemantics.
Require Import ILTranslation.

Lemma translateExp_0 e :
  translateExp 0 e = e.
Proof. Admitted.

Lemma fromExp_translateExp : forall e d,
  fromExp (ILTexprZ (ILTexpr (Tnum 0))) (translateExp (Z.of_nat d) e) = fromExp (ILTexprZ (ILTexpr (Tnum d))) e.
Proof.
  induction e using Exp_ind'.
  Focus 2.
  - intros. simpl. f_equal. f_equal. f_equal.
    replace (Z.of_nat t0' + (i + ILTexprSemZ t0 envT)) with (ILTexprSemZ t0 envT + Z.of_nat t0' + i). eapply H0. ring.
  - intros. simpl. destruct op;
    try (simpl in *; do 3 try (destruct args; try reflexivity); tryfalse; simpl in *;
         unfold bind,compose,pure; apply all_to_forall2 in H; inversion_clear H as [H0 H1];
         rewrite H0; rewrite H1; reflexivity);
    (* Unary operations*)
    try (simpl in *; do 2 try (destruct args; try reflexivity); tryfalse; simpl in *;
         unfold bind,compose,pure; apply all_to_forall1 in H;
         rewrite H; reflexivity).
    
    (* Lit *)
    simpl in *; destruct args; tryfalse; simpl in *; option_inv_auto; tryfalse; subst; simpl in *; some_inv; subst; try reflexivity.
    
    (* cond *)
    simpl in *. do 4 try (destruct args; tryfalse); tryfalse; simpl in *;
    eapply all_to_forall3 in H; inversion_clear H as [IHe1 IHe']; inversion_clear IHe' as [IHe2 IHe3];
    option_inv_auto; subst; simpl in *; try (some_inv); subst.
    simpl in *; subst; option_inv_auto; subst; simpl in *. destruct x0; tryfalse.    
    destruct x;tryfalse.

Lemma translateScale_compile_eq c e d:
  fromContr (Translate (Tnum d) (Scale e c)) (ILTexpr (Tnum 0)) =
  fromContr (Scale (translateExp (Z.of_nat d) e) (Translate (Tnum d) c)) (ILTexpr (Tnum 0)).
Proof.
  simpl. unfold bind,compose,pure. destruct d.
  - simpl. rewrite translateExp_0. reflexivity.
  - simpl. 
