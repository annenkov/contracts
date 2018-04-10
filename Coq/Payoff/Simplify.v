(** Various simplifications/optimisations of payoff expressions *)

Require Import ILSyntax.


(** Replacing [loopif] with just [if] in case is the number of iterations is [Tnum 0] *)
Fixpoint simp_loopif (e : ILExpr) :=
  match e with
  | ILIf cond e1 e2 => ILIf (simp_loopif cond) (simp_loopif e1) (simp_loopif e2)
  | ILFloat r => ILFloat r
  | ILNat n => ILNat n
  | ILBool b => ILBool b
  | ILtexpr t => ILtexpr t
  | ILNow => ILNow
  | ILModel l t => ILModel l t
  | ILUnExpr op e => ILUnExpr op (simp_loopif e)
  | ILBinExpr op e1 e2 => ILBinExpr op (simp_loopif e1) (simp_loopif e2)
  | ILLoopIf cond e1 e2 t =>
    match t with
    | Syntax.Tnum 0 => ILIf (simp_loopif cond) (simp_loopif e1) (simp_loopif e2)
    | _ => ILLoopIf (simp_loopif cond) (simp_loopif e1) (simp_loopif e2) t
    end
  | ILPayoff  t p1 p2 => ILPayoff  t p1 p2
  end.

(* TODO : proof of soundness *)