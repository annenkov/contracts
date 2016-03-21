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
import Data.Maybe

deriving instance Show ILUnOp
deriving instance Show ILBinOp
deriving instance Show ILExpr
deriving instance Show ILVal
deriving instance Show C.Val
deriving instance Eq ILVal
    
translateEuropean  = fromContr (fromHoas european) 0
translateEuropean' = fromContr (fromHoas european') 0
translateWorstOff  = fromContr (fromHoas worstOff) 0

advSimple = fst (advance simple (mkExtEnvP [] []))

transC c = fromMaybe (error "No translation") (fromContr c 0)

trSimple = transC (fromHoas simple)
trAdvSimple = transC (fromHoas advSimple)

advTwoCF = fst (advance twoCF (mkExtEnvP [] []))
trTwoCF = transC (fromHoas twoCF)
trAdvTwoCF = transC $ fromHoas advTwoCF

eval_empty exp = iLsem_k exp [] (\l t -> ILRVal 0) (\t -> 1) X Y

eval k (exp, extEnv)  = iLsem_k exp [] extEnv (\t -> 1) X Y k

sampleExt = mkExtEnvP [(Stock "DJ_Eurostoxx_50", 365, 4100)] []
sampleILExt :: C.ExtEnv' ILVal
sampleILExt = \l t -> if (t == 365) then (ILRVal 4100) else (ILRVal 0)

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
advance1 c env = let (c', _) = fromJust (C.redfun (fromHoas c) [] env)
                in toHoas c'

appProd (f,g) (x,y) = (f x, g y)

path1 :: Int -> (Contr, ExtEnvP) -> Maybe ILVal
path1 k = (eval 0) . (appProd (transC, id)) . (adv_n' k)

path2 :: Int -> (Contr, ExtEnvP) -> Maybe ILVal
path2 k = (eval k) . (appProd (transC . fromHoas, fromExtEnv . fromJustExtEnv))

commute k = path1 k (composite, sampleExt) == path2 k (composite, sampleExt)
  
commute_horizon = and $ map commute [0..(horizon composite)]

-----------
--test :: C.Contr
test = appProd (fromHoas, id) (adv_both 365 (composite, sampleExt))
