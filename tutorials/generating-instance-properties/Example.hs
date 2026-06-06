module Example where

import Numeric.Natural (Natural)

class Foo a where
    foo :: a

prop_bar (x :: Natural) = x == foo

