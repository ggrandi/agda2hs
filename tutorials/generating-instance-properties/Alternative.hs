module Alternative where

instance Alternative Maybe where
    empty = Nothing
    Nothing <|> y = y
    Just x <|> y = Just x

prop_map_empty = True
prop_seq_empty = True
prop_empty_seq = True

