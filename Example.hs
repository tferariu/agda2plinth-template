module Example where

import Lib (PubKeyHash)
import Numeric.Natural (Natural)

example :: Natural -> Natural -> Natural
example a b = if a == b then a else b

example2 :: PubKeyHash -> PubKeyHash -> PubKeyHash
example2 a b = if a == b then a else b

