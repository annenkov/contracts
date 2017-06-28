{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
module Examples.TranslationExample where

import Examples.SampleContracts
import HOAS
import PrettyPrinting
import qualified Contract as C
import qualified RebindableEDSL as R
import EDSL
import ContractTranslation
import Examples.PayoffToHaskell
import Data.Maybe
import qualified Data.Map as Map

deriving instance Show ILUnOp
deriving instance Show ILBinOp
deriving instance Show ILExpr
deriving instance Show TExpr
deriving instance Show ILTExpr
deriving instance Show ILTExprZ
deriving instance Show ILVal
deriving instance Show C.Val
deriving instance Eq ILVal
deriving instance Eq TExpr
deriving instance Eq ILExpr
deriving instance Eq ILTExpr
deriving instance Eq ILTExprZ
deriving instance Eq ObsLabel
deriving instance Eq ILUnOp
deriving instance Eq ILBinOp

tZero = (ILTexpr (C.Tnum 0))
tZeroZ = (ILTexprZ tZero)

empty_tenv :: String -> Int
empty_tenv = (\_ -> undefined)

translateEuropean  = fromContr (fromHoas european) tZero
translateEuropean' = fromContr (fromHoas european') tZero
translateWorstOff  = fromContr (fromHoas worstOff) tZero

                     
advSimple = fst (advance simple (mkExtEnvP [] []) empty_tenv)

transC c = fromMaybe (error "No translation") (fromContr c tZero)

trSimple = transC (fromHoas simple)
trAdvSimple = transC (fromHoas advSimple)

advTwoCF = fst (advance twoCF (mkExtEnvP [] []) empty_tenv)
trTwoCF = transC (fromHoas twoCF)
trAdvTwoCF = transC $ fromHoas advTwoCF

eval_empty exp = iLsem exp (\l t -> ILRVal 0) empty_tenv 0 0 (\t -> 1) X Y

eval k (exp, extEnv)  = iLsem exp extEnv empty_tenv 0 k (\t -> 1) X Y

sampleExt = mkExtEnvP [(Stock "DJ_Eurostoxx_50", 365, 4100)] []
sampleILExt :: C.ExtEnv' ILVal
sampleILExt = \l t -> if (t == 365) then (ILRVal 4100) else (ILRVal 0)

---------------------------------------------------------------
-- Testing, that two paths (reduce, compile than evaluate; and
-- compile, apply cutPayoff and then evaluate) commute
--------------------------------------------------------------              

adv_n :: ExtEnvP -> Int -> Contr -> Contr
adv_n ext 0 c = c
adv_n ext k c = adv_n ext (k-1) (advance1 c ext)

adv_both :: Int -> (Contr, ExtEnvP) -> (Contr, ExtEnvP)
adv_both 0 (c, ext) = (c, ext)
adv_both k (c, ext) = adv_both (k-1) (advance1 c ext, C.adv_ext 1 ext)

fromJustExtEnv ext = \l t -> fromJust (ext l t)
                      
adv_n' :: Int -> (Contr, ExtEnvP) -> (C.Contr, C.ExtEnv' ILVal)
adv_n' k (c, ext) = let (c', ext') = adv_both k (c, ext)
                    in (fromHoas c', fromExtEnv (fromJustExtEnv ext'))

advance1 :: Contr -> ExtEnvP -> Contr
advance1 c env = let (c', _) = fromJust (C.redfun (fromHoas c) [] env empty_tenv)
                in toHoas c'

-- apply product of morphisms
appProd (f,g) (x,y) = (f x, g y)

path1 :: Int -> (Contr, ExtEnvP) -> Maybe ILVal
path1 k = (eval 0) . (appProd (transC, id)) . (adv_n' k)

path2 :: Int -> (Contr, ExtEnvP) -> Maybe ILVal
path2 k = (eval k) . (appProd (cutPayoff . transC . fromHoas, fromExtEnv . fromJustExtEnv))

commute k = path1 k (composite, sampleExt) == path2 k (composite, sampleExt)

-- testing up to the contract horizon
commute_horizon = and $ map commute [0..(horizon composite empty_tenv)]

-----------------------------------------------------------------
-- Some contract equivalences give equal payoff expressions
-- (or up to template expression evaluation)
-----------------------------------------------------------------                  
c1_eq1 = C.Scale (C.OpE (C.RLit 2) []) (C.Scale (C.OpE (C.RLit 3) []) (C.Transfer X Y EUR))
c2_eq1 = C.Scale (C.OpE C.Mult [C.OpE (C.RLit 2) [], C.OpE (C.RLit 3) []]) (C.Transfer X Y EUR)
         
c1_eq2 = C.Translate (C.Tnum 2) $ C.Translate (C.Tnum 3) $ C.Transfer X Y EUR
c2_eq2 = C.Translate (C.Tnum 5) $ C.Transfer X Y EUR

eq2 = transC c1_eq2 == transC c2_eq2

c1_eq3 = C.Translate (C.Tnum 5) $ C.Both (C.Transfer X Y EUR) (C.Transfer X Y EUR)
c2_eq3 = C.Both (C.Translate (C.Tnum 5) $ C.Transfer X Y EUR) (C.Translate (C.Tnum 5) $ C.Transfer X Y EUR)

eq3 = transC c1_eq3 == transC c2_eq3

nonObviouslyCausal = C.Scale (C.Obs (LabR (FX EUR DKK)) 1) (C.Translate (C.Tnum 1) $ C.Transfer X Y EUR)
obviouslyCausal = C.Translate (C.Tnum 1) $ C.Scale (C.Obs (LabR (FX EUR DKK)) 0) (C.Transfer X Y EUR)

eq_causal = transC nonObviouslyCausal == transC obviouslyCausal
