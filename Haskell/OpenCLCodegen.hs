{-# LANGUAGE GADTs #-}

module IntegrationSamples where

import Data.List
import Data.List.Split
import qualified Data.Set as S
import qualified Data.Map as M
import Debug.Trace

import Contract
import LexifiContracts
import Contract.Expr
import Contract.Date
import Contract.Type
import Contract.Transform


-- data type representing AST of some simple imperative language
data CLCode = DeclareVar String String CLCode
            | Assign String CLCode
            | IfStmt CLCode [CLCode] [CLCode]
            | FunCall String [CLCode]
            | BinOp String CLCode CLCode
            | BoolExpr2 String CLCode CLCode
            | BoolNot CLCode  
            | Lit String
            | Var String
            deriving Show

accAssign op name expr = Assign name $ BinOp op (Var name) expr
mulAssign = accAssign "*" 

-- transforming contracts to CLCode
genPayoffFunc c = [amountDecl] ++ body ++ [trajInnerCall]
              where
                amountDecl = DeclareVar "REAL" "amount" $ Lit "1"
                body = genCLCode (Just c) (obsDays c) 0
genCLCode Nothing ds t = []
genCLCode (Just (If cond b1 b2)) ds t =
          IfStmt (genCLExpr cond ds t) (genCLCode (Just b1) ds t) (genCLCode (Just b2) ds t) : []
genCLCode (Just (Transl t' c)) ds t = genCLCode (Just c) ds (t' + t)
genCLCode (Just c) ds t =
          (mulAssign "amount" $ genCLExpr (calcScale e) ds t) : genCLCode rest ds t
          where
            (e, rest) = collectScalings [] c

-- collecting scalings till first "if" or elementary contract such as TransfOne or Zero
collectScalings acc (Scale e c) = collectScalings(e : acc) c
collectScalings acc rest@(Transl _ _) = (acc, Just rest)
collectScalings acc (TransfOne _ _ _) = (acc, Nothing)                
collectScalings acc Zero = (r 0 : acc, Nothing)
collectScalings acc rest@(If _ _ _) = (acc, Just rest)

calcScale [] = (r 1)
calcScale xs = foldl1 (*) xs                

trajInnerCall = FunCall "trajectory_inner"
                        [Var "num_cash_flows", Var "model_num",
                         Lit "0", Var "amount", Var "md_discts",
                         Var "vhat"]
                        
genCLExpr :: Expr a -> [Int] -> Int -> CLCode
genCLExpr (Arith Max e1 e2) ds t = FunCall "fmax" [genCLExpr e1 ds t, genCLExpr e2 ds t]
genCLExpr (Arith Min e1 e2) ds t = FunCall "fmin" [genCLExpr e1 ds t, genCLExpr e2 ds t]
genCLExpr (Arith Minus e1 e2) ds t = BinOp "-" (genCLExpr e1 ds t) (genCLExpr e2 ds t)
genCLExpr (Arith Times e1 e2) ds t = BinOp "*" (genCLExpr e1 ds t) (genCLExpr e2 ds t)
genCLExpr (Arith Div e1 e2) ds t = BinOp "/" (genCLExpr e1 ds t) (genCLExpr e2 ds t)
genCLExpr (Less e1 e2) ds t = BoolExpr2 "<" (genCLExpr e1 ds t) (genCLExpr e2 ds t)
genCLExpr (Or e1 e2) ds t = BoolExpr2 "||" (genCLExpr e1 ds t) (genCLExpr e2 ds t)
genCLExpr (Not e) ds t = BoolNot $ genCLExpr e ds t
genCLExpr (R rLit) ds t = Lit $ show rLit
genCLExpr (Obs (_, t')) ds t
           | (Just i) <- findIndex (== (t' + t)) ds = underlyings (i, 0)
           | otherwise = error $ "no day for " ++ show (t' + t)
           where
                 underlyings (i,j) = FunCall "underlyings" [Lit $ show i, Lit $ show j]

-- pretty-printing OpenCL-like code

ppCLSeq p = (intercalate ";\n" $ map ppCLCode p) ++ ";\n"

ppCLCode (DeclareVar ty name val) = ty ++ " " ++ name ++ surroundBy " " "=" ++ ppCLCode val
ppCLCode (Assign name val) = name ++ spaced "=" ++ ppCLCode val
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

ex4 =
    let strike = 4000.0
        theobs = obs ("Carlsberg",0)
        theobs1 = obs ("Carlsberg",1)
    in scale (r 0.9997817434496459)
             (transl 360
                    (iff (r strike !<! theobs1)
                          (transl 360 $
                           iff (r strike !<! theobs * 2)
                               (scale (theobs*2 - r strike) (transfOne EUR "you" "me"))
                               (scale (theobs1 - r strike)
                                      (transfOne EUR "you" "me")))
                           (transl 180 $ (iff (r strike !<! theobs - 10)
                                              (transl 185 $ scale theobs $ transfOne EUR "you" "me")
                                         zero))))

-- alternative approach (should be simplier :) )

--extracting transfer days

transfDays c = sort $ nub $ tDays c 0
daysToDates startDate = map ((flip addDays) startDate)
mTransfDates (startDate, c) = daysToDates startDate $ transfDays c 

tDays (Scale e c) t = tDays c t
tDays (Transl t' c) t = t' + t : tDays c (t' + t) 
tDays (TransfOne _ _ _) t = []                
tDays Zero _ = []
tDays (If _ c1 c2) t = tDays c1 t ++ tDays c2 t

obsDays c = sort $ nub $ oDays c 0
mObsDates (startDate, c) = daysToDates startDate $ obsDays c

oDays (Scale e c) t = oDaysE e t ++ oDays c t
oDays (Transl t' c) t = oDays c (t' + t) 
oDays (TransfOne _ _ _) t = []                
oDays Zero _ = []
oDays (If e c1 c2) t = oDaysE e t ++ oDays c1 t ++ oDays c2 t 

oDaysE :: Expr a -> Int -> [Int]
oDaysE (Arith _ e1 e2) t = oDaysE e1 t ++ oDaysE e2 t  
oDaysE (Less e1 e2) t = oDaysE e1 t ++ oDaysE e2 t
oDaysE (Or e1 e2) t = oDaysE e1 t ++ oDaysE e2 t
oDaysE (Not e) t = oDaysE e t
oDaysE (R rLit) t = []
oDaysE (Obs (_, t')) t = [t' + t]



-- usage examples
-- putStr $ ppCLSeq $ genPayoffFunc ex2 -- pretty-printing in console
-- writeOpenCL (ppCLSeq $ genPayoffFunc ex2) "SmallContract" -- to generate SmallContract.cl in current directory
