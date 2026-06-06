module MonadPlus where

import Alternative (Alternative(empty, (<|>)))
import Numeric.Natural (Natural)

instance MonadPlus [] where

prop_left_zero (Fun _ (k :: Natural -> [Natural]))
  = (empty >>= k) == (empty :: [Natural])
prop_left_distribution (x :: [Natural]) (y :: [Natural])
  (Fun _ (k :: Natural -> [Natural]))
  = (x <|> y >>= k) == ((x >>= k) <|> (y >>= k))

