module ImplementationExample where

import Numeric.Natural (Natural)
import Test.QuickCheck (Arbitrary(arbitrary, shrink), frequency)

import Prelude hiding (Maybe, Just, Nothing)

data Maybe a = Nothing
             | Just a
                 deriving (Show)

instance Functor Maybe where
    fmap f Nothing = Nothing
    fmap f (Just x) = Just (f x)

prop_identity (fa :: Maybe Natural) = fmap id fa == id fa
prop_composition (fa :: Maybe Natural)
  (Fun _ (f :: Natural -> Natural)) (Fun _ (g :: Natural -> Natural))
  = fmap (g . f) fa == (fmap g . fmap f) fa

instance (Eq a) => Eq (Maybe a) where
    Nothing == Nothing = True
    Nothing == Just y = False
    Just x == Nothing = False
    Just x == Just y = x == y

instance (Arbitrary a) => Arbitrary (Maybe a) where
    arbitrary = frequency [(0, pure Nothing), (4, Just <$> arbitrary)]
    shrink (Just x) = Nothing : (Just <$> shrink x)
    shrink Nothing = []

