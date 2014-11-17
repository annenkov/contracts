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


-- data type representing AST of some simple imperative language
data CLCode = DeclareVar String String CLCode
            | Assign String CLCode
            | MulAssign String CLCode  
            | IfStmt CLCode [CLCode] [CLCode]
            | FunCall String [CLCode]
            | BinOp String CLCode CLCode
            | BoolExpr2 String CLCode CLCode
            | BoolNot CLCode  
            | Lit String
            | Var String
            deriving Show

-- transforming contracts to CLCode
genPayoffFunc c = [amountDecl] ++ body ++ [trajInnerCall]
              where
                (MulAssign "amount" initialAmount : body) = genCLCode [] (Just c)
                amountDecl = DeclareVar "REAL" "amount" initialAmount

genCLCode acc Nothing = acc
genCLCode acc (Just (If cond b1 b2)) =
  acc ++ [IfStmt (genCLExpr cond) (genCLCode [] (Just b1)) (genCLCode [] (Just b2))]
genCLCode acc (Just c) =
  acc ++ [MulAssign "amount" $ genCLExpr $ calcScale e] ++ genCLCode acc rest
    where
      (e, rest) = collectScalings [] c

-- collecting scalings till first "if" or elementary contract such as TransfOne or Zero
collectScalings acc (Scale e c) = collectScalings(e : acc) c
collectScalings acc (Transl _ c) = collectScalings acc c
collectScalings acc (TransfOne _ _ _) = (acc, Nothing)                
collectScalings acc Zero = (r 0 : acc, Nothing)
collectScalings acc rest@(If _ _ _) = (acc, Just rest)

calcScale [] = (r 1)
calcScale xs = foldl1 (*) xs                

trajInnerCall = FunCall "trajectory_inner"
                        [Var "num_cash_flows", Var "model_num",
                         Lit "0", Var "amount", Var "md_discts",
                         Var "vhat"]

genCLExpr :: Expr a -> CLCode
genCLExpr (Arith Max e1 e2) = FunCall "fmax" [genCLExpr e1, genCLExpr e2]
genCLExpr (Arith Min e1 e2) = FunCall "fmin" [genCLExpr e1, genCLExpr e2]
genCLExpr (Arith Minus e1 e2) = BinOp "-" (genCLExpr e1) (genCLExpr e2)
genCLExpr (Arith Times e1 e2) = BinOp "*" (genCLExpr e1) (genCLExpr e2)
genCLExpr (Arith Div e1 e2) = BinOp "/" (genCLExpr e1) (genCLExpr e2)
genCLExpr (Less e1 e2) = BoolExpr2 "<" (genCLExpr e1) (genCLExpr e2)
genCLExpr (Or e1 e2) = BoolExpr2 "||" (genCLExpr e1) (genCLExpr e2)
genCLExpr (Not e) = BoolNot $ genCLExpr e
genCLExpr (R rLit) = Lit $ show rLit
genCLExpr (Obs _) = FunCall "underlyings" [Lit "0", Lit "0"] -- only one uderlying for now

-- pretty-printing OpenCL-like code

ppCLSeq p = (intercalate ";\n" $ map ppCLCode p) ++ ";\n"

ppCLCode (DeclareVar ty name val) = ty ++ " " ++ name ++ surroundBy " " "=" ++ ppCLCode val
ppCLCode (Assign name val) = name ++ spaced "=" ++ ppCLCode val
ppCLCode (MulAssign name val) = name ++ spaced "*=" ++ ppCLCode val
ppCLCode (FunCall name args) = name ++ inParens (commaSeparated $ map ppCLCode args)
ppCLCode (BinOp op e1 e2) = inParens $ ppCLCode e1 ++ surroundBy " " op ++ ppCLCode e2
ppCLCode (BoolExpr2 op e1 e2) = inParens $ ppCLCode e1 ++ surroundBy " " op ++ ppCLCode e2
ppCLCode (BoolNot e) = "!" ++ (inParens $ ppCLCode e)
ppCLCode (IfStmt cond tB fB) = "if" ++ spaced (inParens $ ppCLCode cond) ++
                               (inBlock $ ppCLSeq tB) ++
                               spaced "else" ++ (inBlock $ ppCLSeq fB)
ppCLCode (Lit s) = s
ppCLCode (Var v) = v

-- templates-like replacing
replace this that = intercalate that . splitOn this
replaceLabel label that = replace ("{|" ++ label ++ "|}") that

-- some helpers for pretty-printing
inParens s = "(" ++ s ++ ")"
inCurlBr s = "{" ++ s ++ "}"
newLn s = "\n" ++ s
inBlock = newLn . inCurlBr . newLn
commaSeparated = intercalate ", "
surroundBy c s = c ++ s ++ c
spaced = surroundBy " "

fromManaged (_, c) = c

writeOpenCL p fileName=
  do
    template <- readFile "ContractTemplate.cl"
    writeFile (fileName ++ ".cl") (replaceLabel "CODE" p template)


-- Sample contracts

ex1 = scale 200 $ flow 1 (r 100) EUR "you" "me"

ex2 =
    let strike = 4000.0
        theobs = obs ("Carlsberg",0)
    in scale (r 0.9997817434496459)
             (transl 360
                    (iff (r strike !<! theobs)
                          (scale (theobs - r strike)
                                 (transfOne EUR "you" "me"))
                         zero))

-- like ex2 but with additional condition (just to test nested "if"s)
ex3 =
    let strike = 4000.0
        theobs = obs ("Carlsberg",0)
    in scale (r 0.9997817434496459)
             (transl 360
                    (iff (r strike !<! theobs)
                          ( iff (r strike !<! theobs * 2)
                            (scale (theobs*2 - r strike) (transfOne EUR "you" "me"))
                            (scale (theobs - r strike)
                                 (transfOne EUR "you" "me")))
                         zero))

-- usage examples
-- putStr $ ppCLSeq $ genPayoffFunc ex2 -- pretty-printing in console
-- writeOpenCL (ppCLSeq $ genPayoffFunc ex2) "SmallContract" -- to generate SmallContract.cl in current directory
