module Examples.PayoffToHaskell where

import Data.List

import ContractTranslation
import Contract

funcName = "payoff"
    
fromBinOp op = case op of
                 ILAdd -> "+"
                 ILSub -> "-"
                 ILMult -> "*"
                 ILDiv -> "/"
                 ILAnd -> "&&"
                 ILOr -> "||"
                 ILLess -> "<"
                 ILLessN -> "<"
                 ILLeq -> "<="
                 ILEqual -> "=="

fromUnOp op = case op of
                ILNot -> "not"
                ILNeg -> "-"

fromTexpr e = case e of
                Tnum n -> show n
                Tvar s -> inParens ("tenv Map.! " ++ show s)
                         
fromILTexpr e = case e of
                  ILTplus e1 e2 -> fromILTexpr e1 ++ " + " ++ fromILTexpr e2
                  ILTexpr e -> fromTexpr e

fromILTexprZ e = case e of
                   ILTplusZ e1 e2 -> fromILTexprZ e1 ++ " + " ++ fromILTexprZ e2
                   ILTexprZ e -> fromILTexpr e
                   ILTnumZ n -> show n
                         
fromPayoff e = case e of
                 ILIf e' e1 e2 -> inParens ("if " ++ inParens (fromPayoff e') ++
                                            "then " ++ inParens (fromPayoff e1) ++
                                            "else " ++ inParens (fromPayoff e2))
                 ILFloat v -> show v
                 ILNat n -> show n
                 ILBool b -> show b
                 ILtexpr e -> inParens (fromILTexpr e) ++ " + t0"
                 ILNow -> "t_now"
                 ILModel (LabR (Stock l)) t ->
                     inParens ("ext Map.! " ++ inParens ( surroundBy "\"" l ++ "," ++ inParens (fromILTexprZ t ++ "+ t0")))
                 ILUnExpr op e -> fromUnOp op ++ " " ++ fromPayoff e
                 ILBinExpr op e1 e2 -> inParens (fromPayoff e1 ++ spaced (fromBinOp op) ++ fromPayoff e2)
                 ILLoopIf e e1 e2 t -> "loopif" ++ spaced (inParens (fromTexpr t))
                                                ++ spaced "t0"
                                                ++ spaced (lambda "t0" (fromPayoff e))
                                                ++ spaced (lambda "t0" (fromPayoff e1))
                                                ++ spaced (lambda "t0" (fromPayoff e2))
                 ILPayoff t p1' p2' -> inParens (ifThenElse (show p1' ++ "== p1 && " ++ show p2' ++ "== p2") "1"
                                                                (ifThenElse (show p1' ++ "== p2 && " ++ show p2' ++ "== p1") "-1" "0"))

ppHaskellCode e = funcName ++ " ext tenv t0 t_now p1 p2 = " ++ fromPayoff e
lambda v e = "(\\" ++ v ++ "->" ++ e ++ ")"
-- some helpers for pretty-printing
inParens s = "(" ++ s ++ ")"
inCurlBr s = "{" ++ s ++ "}"
inSqBr s = "[" ++ s ++ "]"
newLn s = "\n" ++ s
inBlock = newLn . inCurlBr . newLn
commaSeparated = intercalate ", "
surroundBy c s = c ++ s ++ c
spaced = surroundBy " "
ifThenElse cond e1 e2 = "if " ++ spaced (inParens cond) ++ "then" ++ spaced e1 ++ "else" ++ spaced e2

header = "module Examples.PayoffFunction where\nimport qualified Data.Map as Map\nimport BaseTypes\nimport Examples.BasePayoff\n"
                        
compileAndWrite exp =
  do
    let out = header ++ ppHaskellCode exp
    writeFile "./Examples/PayoffFunction.hs" out
