{-# LANGUAGE ScopedTypeVariables #-}

module AnalysisPostulated.LawfulApplicativeTuple₂ where


import Test.QuickCheck
import Text.Show.Functions

prop_identity (v :: ([Integer], Integer)) = (pure id <*> v) == v
prop_composition (u :: ([Integer], Integer -> Integer))
  (v :: ([Integer], Integer -> Integer)) (w :: ([Integer], Integer))
  = (pure (.) <*> u <*> v <*> w) == (u <*> (v <*> w))
prop_homomorphism (Fun _ (f :: Integer -> Integer)) (x :: Integer)
  = ((pure f :: ([Integer], Integer -> Integer)) <*> pure x) ==
      pure (f x)
prop_interchange (u :: ([Integer], Integer -> Integer))
  (y :: Integer) = (u <*> pure y) == (pure ($ y) <*> u)
prop_functor (Fun _ (f :: Integer -> Integer))
  (x :: ([Integer], Integer)) = fmap f x == (pure f <*> x)

