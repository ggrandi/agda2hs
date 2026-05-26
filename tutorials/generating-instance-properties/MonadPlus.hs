module MonadPlus where

import Alternative (Alternative (empty, (<|>)))
import Numeric.Natural (Natural)

instance MonadPlus []

prop_left_zero :: (Natural -> [Natural]) -> Bool
prop_left_zero k = (empty >>= k) == (empty :: [Natural])
prop_left_distribution ::
  [Natural] -> [Natural] -> (Natural -> [Natural]) -> Bool
prop_left_distribution x y k =
  (x <|> y >>= k) == ((x >>= k) <|> (y >>= k))
