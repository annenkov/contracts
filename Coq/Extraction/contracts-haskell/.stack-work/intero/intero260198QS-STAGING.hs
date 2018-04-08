module Main where

import Examples.TranslationExample
import Examples.SampleContracts
import HOAS
import PrettyPrinting



main :: IO ()
main = do
  putStrLn "European option:"
  putStrLn $ show $ fromHoas european
  putStrLn "-----------------"
  putStrLn "Corresponding payoff expression:"
  putStrLn $ show $ translateEuropean
