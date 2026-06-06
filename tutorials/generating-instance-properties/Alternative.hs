module Alternative where

import Numeric.Natural (Natural)

instance Alternative Maybe where
    empty = Nothing
    Nothing <|> y = y
    Just x <|> y = Just x

instance Alternative [] where
    empty = []
    x <|> y = x ++ y

prop_map_empty (Fun _ (g :: Natural -> Natural))
  = (g <$> empty) == (empty :: [Natural])
prop_seq_empty (g :: [Natural -> Natural]) = (g <*> empty) == empty
prop_empty_seq (g :: [Natural])
  = (empty <*> g) == (empty :: [Natural])
prop_or_empty (x :: [Natural]) = (x <|> empty) == x
prop_empty_or (x :: [Natural]) = (empty <|> x) == x
prop_or_assoc (x :: [Natural]) (y :: [Natural]) (z :: [Natural])
  = (x <|> (y <|> z)) == (x <|> y <|> z)
prop_map_or (Fun _ (g :: Natural -> Natural)) (x :: [Natural])
  (y :: [Natural]) = (g <$> (x <|> y)) == (g <$> x <|> g <$> y)

