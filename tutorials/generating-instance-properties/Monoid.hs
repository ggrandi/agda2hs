module Monoid where

import Numeric.Natural (Natural)

newtype Add = Add' Natural

instance Eq Add where
    Add' x == Add' y = x == y

instance Semigroup Add where
    Add' x <> Add' y = Add' $ x + y

instance Monoid Add where
    mempty = Add' 0

prop_associativity (x :: Add) (y :: Add) (z :: Add)
  = x <> y <> z == (x <> y) <> z

prop_rightIdentity (x :: Add) = x <> mempty == x
prop_leftIdentity (x :: Add) = mempty <> x == x
prop_concatenation (xs :: [Add])
  = mconcat xs == foldr (<>) mempty xs

