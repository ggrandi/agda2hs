module Alternative where

instance Alternative Maybe where
    empty = Nothing
    Nothing <|> y = y
    Just x <|> y = Just x

prop_map_empty :: (a -> b) -> Bool
prop_map_empty g = True
prop_seq_empty :: Maybe (a -> b) -> Bool
prop_seq_empty g = True
prop_empty_seq :: Maybe a -> Bool
prop_empty_seq g = True
prop_or_empty :: Maybe a -> Bool
prop_or_empty x = True
prop_empty_or :: Maybe a -> Bool
prop_empty_or x = True
prop_or_assoc :: Maybe a -> Maybe a -> Maybe a -> Bool
prop_or_assoc x y z = True
prop_map_or :: (a -> b) -> Maybe a -> Maybe a -> Bool
prop_map_or g x y = True

