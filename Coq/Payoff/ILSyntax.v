(* Add LoadPath "..". *)

Require Import Reals Syntax.

Inductive ILTExpr : Set := ILTplus (e1 : ILTExpr) (e2 : ILTExpr) | ILTexpr (e : TExpr).
Inductive ILTExprZ : Set := ILTplusZ (e1 : ILTExprZ) (e2 : ILTExprZ) | ILTexprZ (e : ILTExpr) | ILTnumZ (z : Z).

Inductive ILBinOp : Set := ILAdd | ILSub | ILMult | ILDiv | ILAnd | ILOr |
                           ILLess | ILLessN  | ILLeq | ILEqual.

Inductive ILUnOp : Set := ILNot | ILNeg.

Inductive ILExpr : Set :=
| ILIf : ILExpr -> ILExpr -> ILExpr -> ILExpr
| ILFloat : R -> ILExpr
| ILNat : nat -> ILExpr
| ILBool : bool -> ILExpr
| ILtexpr : ILTExpr -> ILExpr
| ILNow  :  ILExpr
| ILModel : ObsLabel -> ILTExprZ -> ILExpr
| ILUnExpr : ILUnOp -> ILExpr -> ILExpr
| ILBinExpr : ILBinOp -> ILExpr -> ILExpr -> ILExpr
| ILLoopIf : ILExpr -> ILExpr -> ILExpr -> TExpr -> ILExpr
| ILPayoff  : ILTExpr -> Party -> Party -> ILExpr.
