{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}

module EDSL (
-- * Data types used in contracts
Asset (..),
Party (..),

Exp,
acc,
ife,
-- * Real expression combinators
RExp,
rLit,
rObs,


-- * Boolean expression combinators
BExp,
false, true,
(!<!), (!<=!), (!=!), (!/=!), (!>!), (!>=!), (!&!), (!|!),
bNot,
bObs,

-- * Template expressions
TExpr,
TVar,
-- * Contract combinators
ContrHoas,
Contr,
zero,
transfer,
scale,
(#),
both,
(&),
translate,
translateT,
(!),
ifWithin,
ifWithinT,
iff,
letc,

-- * Operations on contracts
ObsLabel (..),
RealObs (..),
BoolObs (..),
ExtEnvP,
FMap,
horizon,
advance,
specialise,
hasType,
printContr,
showContr,

mkExtEnvP,

ExpHoas,
R, B,

) where

import Contract hiding (Exp,Contr,specialise,horizon,map)
import qualified Contract as C
import HOAS
import qualified Data.Map as Map
import Data.Maybe


horizon ::  Contr -> TEnv -> Int
horizon c tenv = C.horizon (fromHoas c) tenv

advance :: Contr -> ExtEnvP -> TEnv -> (Contr, FMap)
advance c env tenv = let (c',t) = fromJust (redfun (fromHoas c) [] env tenv)
                in (toHoas c', t)

specialise :: Contr -> TEnv -> ExtEnvP -> Contr
specialise c tenv = toHoas . C.specialise (fromHoas c) [] tenv

mkExtEnvP :: [(RealObs, Int,Double)] -> [(BoolObs, Int,Bool)] -> ExtEnvP
mkExtEnvP rs bs = env
    where real (l,i,r) = ((l,i),RVal r)
          bool (l,i,r) = ((l,i),BVal r)
          tabR = Map.fromList (map real rs)
          tabB = Map.fromList (map bool bs)
          env (LabR l) i = Map.lookup (l,i) tabR
          env (LabB l) i = Map.lookup (l,i) tabB


hasType :: TEnv -> Contr -> Bool
hasType tenv = C.has_type tenv . fromHoas

printContr :: Contr -> IO ()
printContr = putStrLn . showContr

showContr :: Contr -> String
showContr = show . fromHoas
