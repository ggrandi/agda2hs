module Haskell.Test.QuickCheck where

open import Haskell.Prelude

postulate
  Gen : Type → Type

  instance
    iFunctorGen : Functor Gen
    iApplicativeGen : Applicative Gen
    iMonadGen : Monad Gen

record Arbitrary (a : Type) : Type where
  field
    arbitrary : Gen a
    shrink : a → List a

open Arbitrary ⦃...⦄ public
{-# COMPILE AGDA2HS Arbitrary existing-class #-}

postulate
  instance
    iArbitraryNat : Arbitrary Nat
    iArbitraryInt : Arbitrary Int
    iArbitraryString : Arbitrary String
    iArbitraryEither : ⦃ _ : Arbitrary a ⦄ → ⦃ _ : Arbitrary b ⦄ → Arbitrary (Either a b)
    iArbitraryTuple₂ : ⦃ _ : Arbitrary a ⦄ → ⦃ _ : Arbitrary b ⦄ → Arbitrary (a × b)
    iArbitraryTuple₃ : ⦃ _ : Arbitrary a ⦄ → ⦃ _ : Arbitrary b ⦄ → ⦃ _ : Arbitrary c ⦄ 
      → Arbitrary (a × b × c)
