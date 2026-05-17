module Simple where

import Numeric.Natural (Natural)

class Foo a where
    bar :: a
    baz :: a
    bar2baz :: a -> a

instance Foo Natural where
    bar = 0
    baz = 1
    bar2baz = suc

prop_bar2baz_of_bar = bar2baz (bar :: Natural) == baz

