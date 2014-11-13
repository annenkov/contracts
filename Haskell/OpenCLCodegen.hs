{-# LANGUAGE GADTs #-}
module IntegrationSamples where

import Data.List
import Data.List.Split

import Contract
import LexifiContracts
import Contract.Expr
import Contract.Date
import Contract.Type
import Contract.Transform


-- data representing AST of some simple imperative language
data CLCode = DeclareVar String String CLCode
              | FunCall String [CLCode]
              | BinOp String CLCode CLCode
              | Lit String
              | Var String
                deriving Show

-- transfroming contracts to CLCode
genCLContr (Scale e c) = DeclareVar "REAL" "amount" (genCLExpr e) : genCLContr c
genCLContr (Transl _ c) = genCLContr c
genCLContr (TransfOne _ _ _) = FunCall "trajectory_inner"
                               [Var "num_cash_flows", Var "model_num",
                                Lit "0", Var "amount", Var "md_discts",
                                Var "vhat"] : []

genCLExpr (Arith Max e1 e2) = FunCall "fmax" [genCLExpr e1, genCLExpr e2]
genCLExpr (Arith Minus e1 e2) = BinOp "-" (genCLExpr e1) (genCLExpr e2)
genCLExpr (R rLit) = Lit $ show rLit
genCLExpr (Obs _) = FunCall "underlyings" [Lit "0", Lit "0"]

-- pretty-printing OpenCL-like (oversimplified) code
ppCLProg p = (intercalate ";\n" $ map ppCLCode p) ++ ";\n"

ppCLCode (DeclareVar ty name val) = ty ++ " " ++ name ++ surroundBy " " "=" ++ ppCLCode val
ppCLCode (FunCall name args) = name ++ inParens (commaSeparated $ map ppCLCode args)
ppCLCode (BinOp op e1 e2) = ppCLCode e1 ++ surroundBy " " op ++ ppCLCode e2
ppCLCode (Lit s) = s
ppCLCode (Var v) = v

--templates
replace this toThat = intercalate toThat . splitOn this
replaceLabel label toThat = replace ("{|" ++ label ++ "|}") toThat

-- some helpers for pretty-printing
inParens s = "(" ++ s ++ ")"
commaSeparated = intercalate ", "
surroundBy c s = c ++ s ++ c

fromManaged (_, c) = c

writeOpenCL p fileName=
  do
    template <- readFile "ContractTemplate.cl"
    writeFile (fileName ++ ".cl") (replaceLabel "CODE" p template)
