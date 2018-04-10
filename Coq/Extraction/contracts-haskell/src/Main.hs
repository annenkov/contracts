module Main where

import Examples.TranslationExample
import Examples.SampleContracts
import qualified ContractTranslation as CT
import qualified Contract as C
import qualified Examples.PayoffToHaskell as H
import qualified Examples.PayoffToFuthark as F
import HOAS
import PrettyPrinting
import Data.List



main :: IO ()
main = do
  putStrLn "European option:"
  putStrLn $ show $ fromHoas european
  putStrLn "-----------------"
  putStrLn "Corresponding payoff expression:"
  putStrLn $ show $ translateEuropean

-- generating Futhark code for the simple barrer contract

tenv = ["maturity"]

barrierInFuthark = putStrLn $ F.ppFutharkCode tenv $ transC (fromHoas barrier)
barrierInFutharkCutPayoff = putStrLn $ F.ppFutharkCode tenv $ CT.cutPayoff $ transC (fromHoas barrier)

writeBarrierCode = F.compileAndWrite "./src/Examples/Futhark/" tenv (CT.cutPayoff $ transC (fromHoas barrier))

compositeInFutharkCutPayoff = putStrLn $ F.ppFutharkCode tenv $ CT.cutPayoff $ transC (fromHoas composite)

-- reindexing according to the order of days.

eo = fromHoas european'

obsDays = C.obsDays eo (\_ -> error "Empty template env")
transDays = C.transfDays eo (\_ -> error "Empty template env")

lookInd t = maybe err id . findIndex (\x -> x == t)
  where err = error $ "Could not find time value: " ++ show t

reindexEo = F.IndT (\t -> lookInd t obsDays) (\t -> lookInd t transDays)

europeanOptInFuthark = putStrLn $ F.ppFutharkCode tenv $ CT.cutPayoff $ CT.simp_loopif $ transC (fromHoas european')
reindexedEuropeanOptInFuthark = putStrLn $ F.ppFutharkCode tenv $ CT.cutPayoff $
  F.reindex reindexEo $ CT.simp_loopif $ transC (fromHoas european')
worstOffInFuthark = putStrLn $ F.ppFutharkCode tenv $ transC (fromHoas worstOff)
