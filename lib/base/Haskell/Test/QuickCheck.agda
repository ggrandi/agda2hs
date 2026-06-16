module Haskell.Test.QuickCheck where

open import Haskell.Prelude

postulate
  Gen : Type → Type

  oneof : (xs : List (Gen a)) ⦃ @0 _ : NonEmpty xs ⦄ → Gen a
  frequency : (xs : List (Int × Gen a))
    -- frequency [] = error "QuickCheck.frequency used with empty list"
    ⦃ @0 non-empty : NonEmpty xs ⦄
    -- frequency xs
    -- | any (< 0) (map fst xs) = error "QuickCheck.frequency: negative weight"
    ⦃ @0 non-negative : IsFalse (any (_< 0) (map fst xs)) ⦄
    -- | all (== 0) (map fst xs) = error "QuickCheck.frequency: all weights were zero"
    ⦃ @0 non-zero : IsFalse (all (_== 0) (map fst xs)) ⦄
    → Gen a

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
