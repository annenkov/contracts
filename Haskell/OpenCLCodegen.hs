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
                body = genCLCode (0, 0) (daysEnv c) (Just c)

genCLCode _ dEnv Nothing = []
genCLCode tr@(n, cTran) dEnv (Just (If cond b1 b2)) =ppCLCode (MulAssign name val) = name ++ spaced "*=" ++ ppCLCode val
          IfStmt (genCLExpr (tr, dEnv) cond) (genCLCode tr dEnv (Just b1)) (genCLCode tr dEnv (Just b2)) : []
genCLCode (n, cTran) dEnv (Just (Transl d c)) = genCLCode (n+1, d) dEnv (Just c)
genCLCode tr@(n, cTran) dEnv (Just c) =
          (mulAssign "amount" $ genCLExpr (tr, dEnv) (calcScale e)) : genCLCode tr dEnv rest
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

genCLExpr :: ((Int, Int), [(Int,S.Set (Int, Int))]) -> Expr a -> CLCode
genCLExpr n (Arith Max e1 e2) = FunCall "fmax" [genCLExpr n e1, genCLExpr n e2]
genCLExpr n (Arith Min e1 e2) = FunCall "fmin" [genCLExpr n e1, genCLExpr n e2]
genCLExpr n (Arith Minus e1 e2) = BinOp "-" (genCLExpr n e1) (genCLExpr n e2)
genCLExpr n (Arith Times e1 e2) = BinOp "*" (genCLExpr n e1) (genCLExpr n e2)
genCLExpr n (Arith Div e1 e2) = BinOp "/" (genCLExpr n e1) (genCLExpr n e2)
genCLExpr n (Less e1 e2) = BoolExpr2 "<" (genCLExpr n e1) (genCLExpr n e2)
genCLExpr n (Or e1 e2) = BoolExpr2 "||" (genCLExpr n e1) (genCLExpr n e2)
genCLExpr n (Not e) = BoolNot $ genCLExpr n e
genCLExpr n (R rLit) = Lit $ show rLit
genCLExpr ((l, days), dEnv) (Obs (_, d))
          | (Just i) <- dayIndex (chooseDay d, l) dEnv  = underlyings (i, 0)
          | otherwise = error $ "No day for " ++ show (chooseDay d, l)
          where
            chooseDay d | d /= 0 = d
                        | otherwise = days
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

getTranslations (Scale e c) = getTranslations c
getTranslations tr@(Transl d c) = d : getTranslations c 
getTranslations (TransfOne _ _ _) = []               
getTranslations Zero = []
getTranslations (If _ b1 b2) = getTranslations b1 ++ getTranslations b2
getTranslations (Both c1 c2) = getTranslations c1 ++ getTranslations c2

data BranchingSeq a = Seq a (BranchingSeq a)
                    | Split (BranchingSeq a) (BranchingSeq a)
                    | Leaf
                    deriving Show

getDays :: Bool -> Contract -> BranchingSeq Int
getDays all (Scale e c) = listToBrSeq (nonZeroShifts $ getObs e) $ getDays all c
getDays all tr@(Transl d c) = Seq d (getDays all c)
getDays all (TransfOne _ _ _) = Leaf           
getDays all Zero = Leaf
getDays all (If e b1 b2) | all = listToBrSeq (nonZeroShifts $ getObs e) $ Split (getDays all b1) (getDays all b2)
                         | otherwise = Split (getDays all b1) (getDays all b2)
getDays all (Both c1 c2) = Split (getDays all c1) (getDays all c2)

getAllDays = getDays True
getTransfDays = getDays False

listToBrSeq [] end = end
listToBrSeq (x:[]) end = Seq x end
listToBrSeq (x:xs) end = Seq x (listToBrSeq xs end)

getObs :: Expr a -> [(String, Int)]
getObs (Arith _ e1 e2) = getObs e1 ++ getObs e2   
getObs (Less e1 e2) = getObs e1 ++ getObs e2
getObs (Or e1 e2) = getObs e1 ++ getObs e2
getObs (Not e) = getObs e
getObs (R rLit) = []
getObs (Obs (name, days)) = [(name, days)]

-- finding non-zero day shifts for observables represented as pairs (name, days)
nonZeroShifts xs = [d | (_, d) <- xs, d > 0]

paths Leaf = [[]]
paths (Split Leaf Leaf) = [[]]
paths (Seq d (Split Leaf Leaf)) = [[d]]
paths (Seq d (Split b1 b2)) = do
  b <- [b1, b2]
  map (d :) (paths b)
paths (Seq d c) = map (d :) $ paths c 


accDates dss = map accD dss
             where
               accD = scanl1 (+)
-- returns [(<accumulated_shift_in_days>, <set of tuples (<translation_days, <level_in_branching_seq>>)>)]
-- we should have discount values for every day listed in returned list
daysEnv c = M.toList $ M.fromListWith (S.union) $ map valToSet $ concat $
             zipWith3 (zipWith3 toKeyVal) (accDates ps) ps levelNums
           where
             levelNums = replicate (length ps) [1..]
             toKeyVal accD d i = (accD, [(d, i)])
             ps = paths $ getAllDays c
             valToSet (accD, val) = (accD, S.fromList val)

dayIndex at dEnv = findIndex (S.member at) (map snd dEnv)

daysToDates startDate dEnv = map ((flip addDays) startDate . fst ) dEnv
mDaysToDates (startDate, c) = daysToDates startDate $ daysEnv c 

-- usage examples
-- putStr $ ppCLSeq $ genPayoffFunc ex2 -- pretty-printing in console
-- writeOpenCL (ppCLSeq $ genPayoffFunc ex2) "SmallContract" -- to generate SmallContract.cl in current directory
