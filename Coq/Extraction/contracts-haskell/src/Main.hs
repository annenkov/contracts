module Main where

import Examples.TranslationExample
import Examples.SampleContracts
import qualified ContractTranslation as CT
import qualified Examples.PayoffToHaskell as H
import qualified Examples.PayoffToFuthark as F
import HOAS
import PrettyPrinting



main :: IO ()
main = do
  putStrLn "European option:"
  putStrLn $ show $ fromHoas european
  putStrLn "-----------------"
  putStrLn "Corresponding payoff expression:"
  putStrLn $ show $ translateEuropean

-- generation Futhark code for the barrer oprion

tenv = ["maturity"]

barrierInFuthark = putStrLn $ F.ppFutharkCode tenv $ transC (fromHoas barrier)
barrierInFutharkCutPayoff = putStrLn $ F.ppFutharkCode tenv $ CT.cutPayoff $ transC (fromHoas barrier)

compositeInFutharkCutPayoff = putStrLn $ F.ppFutharkCode tenv $ CT.cutPayoff $ transC (fromHoas composite)

worstOffInFuthark = putStrLn $ F.ppFutharkCode tenv $ transC (fromHoas worstOff)
