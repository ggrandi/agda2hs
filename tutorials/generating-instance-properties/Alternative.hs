module Alternative where

import Numeric.Natural (Natural)

instance Alternative Maybe where
    empty = Nothing
    Nothing <|> y = y
    Just x <|> y = Just x

instance Alternative [] where
    empty = []
    x <|> y = x ++ y

prop_map_empty :: (Natural -> Natural) -> Bool
prop_map_empty g = (g <$> empty) == (empty :: [Natural])
prop_seq_empty :: [Natural -> Natural] -> Bool
prop_seq_empty g = (g <*> empty) == empty
prop_empty_seq :: [Natural] -> Bool
prop_empty_seq g = (empty <*> g) == (empty :: [Natural])
prop_or_empty :: [Natural] -> Bool
prop_or_empty x = (x <|> empty) == x
prop_empty_or :: [Natural] -> Bool
prop_empty_or x = (empty <|> x) == x
prop_or_assoc :: [Natural] -> [Natural] -> [Natural] -> Bool
prop_or_assoc x y z = (x <|> (y <|> z)) == (x <|> y <|> z)
prop_map_or ::
            (Natural -> Natural) -> [Natural] -> [Natural] -> Bool
prop_map_or g x y = (g <$> (x <|> y)) == (g <$> x <|> g <$> y)

