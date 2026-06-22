module AnalysisPostulated.LawfulFunctorTuple₂ where

import Test.QuickCheck

prop_identity (fa :: (Integer, Integer)) = fmap id fa == id fa
prop_composition (fa :: (Integer, Integer))
  (Fun _ (f :: Integer -> Integer)) (Fun _ (g :: Integer -> Integer))
  = fmap (g . f) fa == (fmap g . fmap f) fa

