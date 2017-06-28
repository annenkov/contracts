module Examples.HaskellPayoff where

import qualified Data.Map as Map
import Contract
import BaseTypes
import Examples.PayoffFunction
import Examples.TranslationExample

ext :: Map.Map (String,Int) Double
ext = Map.fromList [(("DJ_Eurostoxx_50", i), 5000.0 - fromIntegral i)| i <- [0..365]]
{-
test1 = payoff ext empty_tenv 0 0 X Y == 100

-- switching parties
test1_op = payoff ext empty_tenv 0 0 Y X == -100
-}
