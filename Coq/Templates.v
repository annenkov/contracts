(* Proofs and definitions related to contract with template variables*)
Require Import Syntax.

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
