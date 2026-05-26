module Monoid where

import Numeric.Natural (Natural)

newtype Add = Add' Natural

instance Eq Add where
    Add' x == Add' y = x == y

instance Semigroup Add where
    Add' x <> Add' y = Add' $ x + y

instance Monoid Add where
    mempty = Add' 0

prop_associativity :: Add -> Add -> Add -> Bool
prop_associativity x y z = x <> y <> z == (x <> y) <> z

prop_rightIdentity :: Add -> Bool
prop_rightIdentity x = x <> mempty == x
prop_leftIdentity :: Add -> Bool
prop_leftIdentity x = mempty <> x == x
prop_concatenation :: [Add] -> Bool
prop_concatenation xs = mconcat xs == foldr (<>) mempty xs

