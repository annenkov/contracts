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
            | Skip  
            deriving Show

accAssign op name expr = Assign name $ BinOp op (Var name) expr
mulAssign = accAssign "*" 

-- transforming contracts to CLCode
genPayoffFunc c = amountDecl : body
              where
                amountDecl = DeclareVar "REAL" "amount" $ Lit "1"
                body = genCLCode (Just c) (obsDays c) (transfDays c) 0 0

genCLCode Nothing ods tds t ot = []
genCLCode (Just (TransfOne _ _ _)) ods tds t ot
          | (Just i) <- findIndex (== t) tds = [trajInner i]
          | otherwise = error $ "no day for " ++ show t
genCLCode (Just (If cond b1 b2)) ods tds t ot  =
          IfStmt (genCLExpr cond ods ot) (genCLCode (Just b1) ods tds t ot) (genCLCode (Just b2) ods tds t ot) : []
genCLCode (Just (Transl t' c)) ods tds t ot = genCLCode (Just c) ods tds (t' + t) (t' + ot)
genCLCode (Just (CheckWithin e t' c1 c2)) ods tds t ot=
          map genIf [t .. t'+t]
          where
            genIf t'' = IfStmt (genCLExpr e ods t'')
                        (genCLCode (Just c1) ods tds t (t'' + ot))
                        (genCLCode (Just c2) ods tds t (t'' + ot))
genCLCode (Just c) ods tds t ot
          | null e = Skip : genCLCode rest ods tds t ot
          | otherwise =  (mulAssign "amount" $ genCLExpr (calcScale e) ods ot) : genCLCode rest ods tds t ot
          where
            (e, rest) = collectScalings [] c

-- collecting scalings till first "if", "checkWithin" or elementary contract such as TransfOne or Zero
collectScalings acc (Scale e c) = collectScalings(e : acc) c
collectScalings acc rest@(Transl _ _) = (acc, Just rest)
collectScalings acc transf@(TransfOne _ _ _) = (acc, Just transf)                
collectScalings acc Zero = (acc, Nothing)
collectScalings acc rest@(If _ _ _) = (acc, Just rest)
collectScalings acc rest@(CheckWithin _ _ _ _) = (acc, Just rest)

calcScale [] = (r 1)
calcScale xs = foldl1 (*) xs                

trajInner day = FunCall "trajectory_inner"
                        [Var "num_cash_flows", Var "model_num",
                         Lit $ show day, Var "amount", Var "md_discts",
                         Var "vhat"]
                        
genCLExpr :: Expr a -> [Int] -> Int -> CLCode
genCLExpr (Arith Max e1 e2) ods t = FunCall "fmax" [genCLExpr e1 ods t, genCLExpr e2 ods t]
genCLExpr (Arith Min e1 e2) ods t = FunCall "fmin" [genCLExpr e1 ods t, genCLExpr e2 ods t]
genCLExpr (Arith Minus e1 e2) ods t = BinOp "-" (genCLExpr e1 ods t) (genCLExpr e2 ods t)
genCLExpr (Arith Times e1 e2) ods t = BinOp "*" (genCLExpr e1 ods t) (genCLExpr e2 ods t)
genCLExpr (Arith Div e1 e2) ods t = BinOp "/" (genCLExpr e1 ods t) (genCLExpr e2 ods t)
genCLExpr (Less e1 e2) ods t = BoolExpr2 "<" (genCLExpr e1 ods t) (genCLExpr e2 ods t)
genCLExpr (Or e1 e2) ods t = BoolExpr2 "||" (genCLExpr e1 ods t) (genCLExpr e2 ods t)
genCLExpr (Not e) ods t = BoolNot $ genCLExpr e ods t
genCLExpr (R rLit) ods t = Lit $ show rLit
genCLExpr (Obs (_, t')) ods t
           | (Just i) <- findIndex (== (t' + t)) ods = underlyings (i, 0)
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
ppCLCode Skip = ""
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
equity = "Carlsberg"
maturity = 30
ex5 = checkWithin (strike !<! theobs) maturity
                    (scale (theobs - strike) (transfOne EUR "you" "me")) zero
    where strike = r 50.0
          theobs = obs (equity,0)
       
--extracting transfer days

transfDays c = sort $ nub $ tDays c 0
daysToDates startDate = map ((flip addDays) startDate)
mTransfDates (startDate, c) = daysToDates startDate $ transfDays c 

tDays (Scale e c) t = tDays c t
tDays (Transl t' c) t = tDays c (t' + t)
tDays (CheckWithin _ _ c1 c2) t = tDays c1 t ++ tDays c2 t
tDays (TransfOne _ _ _) t = [t]                
tDays Zero _ = []
tDays (If _ c1 c2) t = tDays c1 t ++ tDays c2 t


--extracting observable days
obsDays c = sort $ nub $ oDays c 0
mObsDates (startDate, c) = daysToDates startDate $ obsDays c

oDays (Scale e c) t = oDaysE e t ++ oDays c t
oDays (Transl t' c) t = oDays c (t' + t)
oDays (If e c1 c2) t = oDaysE e t ++ oDays c1 t ++ oDays c2 t
oDays (CheckWithin e t' c1 c2) t = concat (map (oDaysE e) [t .. t+t']) ++ oDays c1 t ++ oDays c2 t
oDays (TransfOne _ _ _) t = []                
oDays Zero _ = []

oDaysE :: Expr a -> Int -> [Int]
oDaysE (Arith _ e1 e2) t = oDaysE e1 t ++ oDaysE e2 t  
oDaysE (Less e1 e2) t = oDaysE e1 t ++ oDaysE e2 t
oDaysE (Or e1 e2) t = oDaysE e1 t ++ oDaysE e2 t
oDaysE (Not e) t = oDaysE e t
oDaysE (R rLit) t = []
oDaysE (Obs (_, t')) t = [t' + t]

discount :: Double -> Int -> Double
discount r t = exp (-r * yearFraction)
               where
                 yearFraction = fromIntegral t/360

-- usage examples
-- putStr $ ppCLSeq $ genPayoffFunc ex2 -- pretty-printing in console
-- writeOpenCL (ppCLSeq $ genPayoffFunc ex2) "SmallContract" -- to generate SmallContract.cl in current directory
