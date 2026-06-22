{-# LANGUAGE ScopedTypeVariables #-}

module AnalysisPostulated.LawfulMonadTuple₂ where


import Test.QuickCheck
import Text.Show.Functions

prop_leftIdentity (x :: Integer)
  (Fun _ (k :: Integer -> ([Integer], Integer)))
  = (return x >>= k) == k x
prop_rightIdentity (ma :: ([Integer], Integer))
  = (ma >>= return) == ma
prop_associativity (ma :: ([Integer], Integer))
  (Fun _ (f :: Integer -> ([Integer], Integer)))
  (Fun _ (g :: Integer -> ([Integer], Integer)))
  = do x <- ma
       f x >>= g
      == (ma >>= f >>= g)
prop_def_seq_bind (ma :: ([Integer], Integer))
  (mb :: ([Integer], Integer))
  = do ma
       mb
      ==
      do x <- ma
         mb
prop_def_pure_return (x :: Integer)
  = (pure x :: ([Integer], Integer)) == return x
prop_def_fmap_bind (Fun _ (f :: Integer -> Integer))
  (ma :: ([Integer], Integer)) = fmap f ma == (ma >>= return . f)
prop_def_zap_bind (mab :: ([Integer], Integer -> Integer))
  (ma :: ([Integer], Integer))
  = (mab <*> ma) ==
      do f <- mab
         x <- ma
         return (f x)

