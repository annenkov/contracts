module Examples.PayoffFunction where
import qualified Data.Map as Map
import BaseTypes
import Examples.BasePayoff
payoff ext tenv t0 t_now p1 p2 =
    (loopif ((tenv Map.! "maturity"))  t0  (\t0->((ext Map.! ("DJ_Eurostoxx_50",(0 + 0+ t0))) <= 4000.0))
                (\t0->0.0)
                (\t0->(2000.0 *
                   (if (((0) + t0 < t_now))then (0.0)
                    else ((if  (X== p1 && Y== p2) then 1 else if  (X== p2 && Y== p1) then -1 else 0  )))))
    + (100.0 * (if (((0) + t0 < t_now))then (0.0)else ((if  (X== p1 && Y== p2) then 1 else if  (X== p2 && Y== p1) then -1 else 0  )))))
