(* Proofs and definitions related to contract with template variables*)
Require Import Syntax.
Require Import Denotational.

(* Predicate on contract template that holds only if contract does not contain template variables  *)
Inductive IsClosedCT : Contr -> Prop :=
| c_closed_zero : IsClosedCT Zero
| c_closed_let c : forall e, IsClosedCT c -> IsClosedCT (Let e c)
| c_closed_transfer cur p1 p2 : IsClosedCT (Transfer cur p1 p2)
| c_closed_scale e c : IsClosedCT c -> IsClosedCT (Scale e c)
| c_closed_translate n c : IsClosedCT c -> IsClosedCT (Translate (Tnum n) c)
| c_closed_both c1 c2 : IsClosedCT c1 -> IsClosedCT c2 -> IsClosedCT (Both c1 c2)
| c_closed_if n e c1 c2: IsClosedCT c1 -> IsClosedCT c2  -> IsClosedCT (If e (Tnum n) c1 c2)
.

(* Instantiate template variables according to tenv *)
Fixpoint inst_contr c tenv :=
  match c with
    | Zero => Zero
    | Let e c' => Let e (inst_contr c' tenv)
    | Transfer p1 p2 a => Transfer p1 p2 a
    | Scale e c' => Scale e (inst_contr c' tenv)
    | Translate texp c' => Translate (Tnum (TexprSem texp tenv)) (inst_contr c' tenv)
    | Both c' c'' => Both (inst_contr c' tenv) (inst_contr c'' tenv)
    | If e texp c' c'' => If e (Tnum (TexprSem texp tenv)) (inst_contr c' tenv) (inst_contr c'' tenv)
  end.

Hint Constructors IsClosedCT.

Lemma inst_contr_IsClosedCT c tenv :
  IsClosedCT (inst_contr c tenv).
Proof.
  induction c; simpl; auto.
Qed.
