module Simple where

import Numeric.Natural (Natural)

class Foo a where
    bar :: a
    baz :: a
    bar2baz :: a -> a
    bar2baz2 :: a -> a

instance Foo Natural where
    bar = 0
    baz = 1
    bar2baz = (+ 1)
    bar2baz2 = (1 +)

prop_bar2baz_of_bar :: Bool
prop_bar2baz_of_bar = bar2baz (bar :: Natural) == baz
prop_bar2baz_eq_bar2baz2 :: Natural -> Bool
prop_bar2baz_eq_bar2baz2 x = bar2baz x == bar2baz2 x

