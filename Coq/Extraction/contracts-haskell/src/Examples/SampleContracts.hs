{-# LANGUAGE RebindableSyntax #-}

module Examples.SampleContracts where

import RebindableEDSL
import qualified Contract as C
import qualified Prelude as P
import Data.Time (Day, diffDays)
import Data.Time.Format (parseTimeOrError, formatTime, defaultTimeLocale)

simple :: Contr
simple = 100 # (transfer X Y EUR)

twoCF :: Contr
twoCF = both (10 # (transfer X Y EUR)) (translate 1 (100 # (transfer X Y EUR)))

barrier :: Contr
barrier = if (theObs <= barrier) `withinT` maturity
           then zero
           else (payment # (transfer X Y EUR))
    where theObs = rObs (Stock "DJ_Eurostoxx_50") 0
          barrier = 4000
          payment = 2000
          maturity = C.Tvar "maturity"

european :: Contr
european = translate 365 
            ((max 0 (theObs - strike)) # (transfer X Y EUR))
            where theObs = rObs (Stock "DJ_Eurostoxx_50") 0
                  strike   = 4000

european' :: Contr
european' = translate 365 
            (if strike < theObs
             then (theObs - strike) # (transfer X Y EUR)
             else zero)
            where
              theObs = rObs (Stock "DJ_Eurostoxx_50") 0
              strike   = 4000

european'' :: Contr
european'' = translate 100 
            (if strike < theObs
             then (theObs - strike) # (transfer X Y EUR)
             else zero)
            where
              theObs = rObs (Stock "AAPL") 0
              strike   = 3000

composite :: Contr
composite = european' & (366 ! simple)

twoOptions :: Contr
twoOptions = european' & european''

-- example of a contract template from Danil's thesis
templateEx :: Contr
templateEx = translateT (C.Tvar "t0")
                 (both (100 # (transfer X Y EUR))
                       (translateT (C.Tvar "t1")
                          (if (100 < theObs)
                           then (theObs * 100) # (transfer X Y EUR)
                           else zero)))
  where
    theObs = rObs (Stock "AAPL") 0

-- worst-off contract on five fixed dates (chain of iff)
worstOff :: Contr
worstOff = P.foldr mkDateCheck endCase (P.zip dDiffs premiums)
    where start  = at "2012-01-27"
          dates  = P.map (\s -> at (show s P.++ "-01-27")) [2013..2017]
          dDiffs   = P.map P.fromIntegral (P.zipWith (P.flip diffDays) (start:dates) dates)
          premiums = [1150.0, 1300.0, 1450.0, 1600.0, 1750]
          -- on the five dates (offset): one below initial spot => pay premium
          mkDateCheck (offset, premium) cont
              = translate offset (if barrier then (collectEUR premium) else cont)
          barrier = not (P.foldl1 min (P.zipWith mkDiff idxs spots) < 0)
          -- MEMO we should have <= , > and >= as smart constructors
          mkDiff idx spot = rObs idx  0 - spot
           -- MEMO we should have RealE division.
          idxs   = P.map Stock [ "DJ_Eurostoxx_50", "Nikkei_225", "SP_500" ]
          spots  = [ 3758.05, 11840, 1200 ]
          -- if end (date 5) reached: pay 1000 if all above 0.75,
          -- otherwise pay the fraction of the worst (HOW? no division)
          endCase = iff (allAbove 0.75) (collectEUR 1000) 
                        (collectEUR (1000 * minRatio))
          minRatio = P.foldl1 min
                            (P.zipWith (\id sp -> rObs id 0 / sp) idxs spots)
          allAbove d = not (P.foldl1 (!|!) 
                             (P.zipWith (fractionSmaller d) idxs spots))
           {- 0.75 < minimum [ obs(id,0) / sp | (id, sp) <- zip idxs spots ]
                               <==> 
              and [ 0.75 * sp !<! obs (id, 0) | (id, sp) <- zip idxs spots ]
                               <==> 
            not (or [obs(id, 0) !<! 0.75 * sp | (id, sp) <- zip idxs spots]) -}
          fractionSmaller d idx spot = rObs idx 0 < d * spot
          collectEUR amount = scale amount (transfer X Y EUR)
          at = parseDate

parseDate = parseTimeOrError True defaultTimeLocale "%Y-%m-%d"

