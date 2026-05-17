module Alternative where

instance Alternative Maybe where
    empty = Nothing
    Nothing <|> y = y
    Just x <|> y = Just x

