{-# LANGUAGE FlexibleContexts, StandaloneDeriving #-}
module Examples.TranslationExample where

import Examples.SampleContracts
import HOAS
import PrettyPrinting
import qualified Contract as C
import qualified RebindableEDSL as R
import EDSL
import ContractTranslation

deriving instance Show ILUnOp
deriving instance Show ILBinOp
deriving instance Show ILExpr
    
translateEuropean  = fromContr (fromHoas european) 0
translateEuropean' = fromContr (fromHoas european') 0
translateWorstOff  = fromContr (fromHoas worstOff) 0

