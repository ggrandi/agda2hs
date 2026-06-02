module Example where

import Numeric.Natural (Natural)

class Foo a where
    foo :: a

prop_bar :: Foo Natural => Natural -> Bool
prop_bar x = x == foo

