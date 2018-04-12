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

paramEnv = F.Params ["DJ_Eurostoxx_50"] ["maturity"]

barrierInFuthark = putStrLn $ F.ppFutharkCode paramEnv $ transC (fromHoas barrier)
barrierInFutharkCutPayoff = putStrLn $ F.ppFutharkCode paramEnv $ CT.cutPayoff $ transC (fromHoas barrier)

writeBarrierCode = F.compileAndWrite "./src/Examples/Futhark/" paramEnv (CT.cutPayoff $ transC (fromHoas barrier))

compositeInFutharkCutPayoff = putStrLn $ F.ppFutharkCode paramEnv $ CT.cutPayoff $ transC (fromHoas composite)

-- reindexing according to the order of days.
eo = fromHoas european'

obsDays = C.obsDays eo (\_ -> error "Empty template env")
transDays = C.transfDays eo (\_ -> error "Empty template env")

lookInd t = maybe err id . findIndex (\x -> x == t)
  where err = error $ "Could not find time value: " ++ show t
reindexEo = F.IndT (\t -> lookInd t obsDays) (\t -> lookInd t transDays)

europeanOptInFuthark = putStrLn $ F.ppFutharkCode paramEnv $ CT.cutPayoff $ CT.simp_loopif $ transC (fromHoas european')
reindexedEuropeanOptInFuthark = putStrLn $ F.ppFutharkCode paramEnv $ CT.cutPayoff $
  F.reindex reindexEo $ CT.simp_loopif $ transC (fromHoas european')


-- twoOptions is a contract consisting of two european options on different observables and with different maturity

reindexTwo = F.IndT (\t -> lookInd t od) (\t -> lookInd t td)
  where
    c = fromHoas twoOptions
    od = C.obsDays c F.empty_tenv
    td = C.transfDays c F.empty_tenv

paramEnv2 = F.Params ["DJ_Eurostoxx_50", "AAPL"] []

-- corresponding payoff expression (simp_loopif used to replace "loopif" with zero iterations by ordinary "if")
twoOptPayoff = CT.simp_loopif $ transC (fromHoas twoOptions)

reindexedTwoOptInFuthark = F.ppFutharkCode paramEnv2 $
                           CT.cutPayoff $
                           F.reindex reindexTwo $ twoOptPayoff

-- wrapping the whole thing to the module
asFutharkModule = F.wrapInModule "PayoffLang" reindexedTwoOptInFuthark

-- just testing how it works for bigger contracts
paramEnv3 = F.Params [ "DJ_Eurostoxx_50", "Nikkei_225", "SP_500" ] []
worstOffInFuthark = F.ppFutharkCode paramEnv3 $ transC (fromHoas worstOff)
