Add LoadPath "..".

Require Import Reals Syntax.

Inductive ILTExpr : Set := ILTnumZ (z : Z) | ILTexpr (e : TExpr). 

Inductive ILBinOp : Set := ILAdd | ILSub | ILMult | ILDiv | ILAnd | ILOr |
                           ILLess | ILLeq | ILEqual.

Inductive ILUnOp : Set := ILNot | ILNeg.

Inductive ILExpr : Set :=
| ILIf : ILExpr -> ILExpr -> ILExpr -> ILExpr
| FloatV : R -> ILExpr
| Model : ObsLabel -> list ILTExpr -> ILExpr
| ILUnExpr : ILUnOp -> ILExpr -> ILExpr
| ILBinExpr : ILBinOp -> ILExpr -> ILExpr -> ILExpr
| ILLoopIf : ILExpr -> ILExpr -> ILExpr -> TExpr -> ILExpr
| Payoff  : list ILTExpr -> Party -> Party -> ILExpr.
