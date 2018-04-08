module Examples.BasePayoff where
import Debug.Trace

{-
Semantics in Coq almost directly translates to a primitive "loopif" in Haskell
Fixpoint loop_if_sem n t0 b e1 e2 : option ILVal:=
  b t0 >>=
       fun b' => match b' with
                   | ILBVal true => e1 t0
                   | ILBVal false =>
                     match n with
                       | O => e2 t0
                       | S n' => loop_if_sem n' (S t0) b e1 e2
                     end                                               
                   | _ => None
                 end. 
-}

loopif :: Int -> Int -> (Int -> Bool) -> (Int -> a) -> (Int -> a) -> a
loopif n t0 b e1 e2 = let b' = b t0 in
                      case b' of
                        True -> e1 t0
                        False -> case n of
                                   0 -> e2 t0
                                   _ -> loopif (n-1) (t0+1) b e1 e2
