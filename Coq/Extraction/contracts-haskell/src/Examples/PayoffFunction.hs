module Examples.PayoffFunction where
import qualified Data.Map as Map
import BaseTypes
import Examples.BasePayoff
payoffInternal ext tenv t0 t_now p1 p2=
  (100.0 * (if  (X== p1 && Y== p2) then 1 else
               if  (X== p2 && Y== p1) then -1 else 0)) +
   loopif 0 t0
     (\t0->(100.0 < (ext Map.! ("AAPL",(0 + (tenv Map.! "t1") + (tenv Map.! "t0")+ t0)))))
     (\t0->(((ext Map.! ("AAPL",(0 + (tenv Map.! "t1") + (tenv Map.! "t0")+ t0)))
              * 100.0) * (if (X== p1 && Y== p2) then 1 else
                             if  (X== p2 && Y== p1) then -1 else 0)))
     (\t0->0.0)
payoff ext tenv t_now p1 p2=payoffInternal ext tenv 0 t_now p1 p2
