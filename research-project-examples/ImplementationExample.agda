module ImplementationExample where

{-# FOREIGN AGDA2HS import Prelude hiding (Maybe, Just, Nothing) #-}

open import Haskell.Prelude hiding (Maybe; Just; Nothing; iEqMaybe; iFunctorMaybe; iDefaultFunctorMaybe)

open import Haskell.Test.QuickCheck

open import Haskell.Law.Eq hiding (iLawfulEqMaybe)
open import Haskell.Law.Functor hiding (iLawfulFunctorMaybe)
open import Haskell.Law.Equality

open import Haskell.Extra.Dec

data Maybe (a : Type) : Type where
  Nothing : Maybe a
  Just : a → Maybe a

{-# COMPILE AGDA2HS Maybe deriving (Show) #-}

instance
  iDefaultFunctorMaybe : DefaultFunctor Maybe
  iFunctorMaybe : Functor Maybe

  iFunctorMaybe = record{DefaultFunctor iDefaultFunctorMaybe}
  iDefaultFunctorMaybe .DefaultFunctor.fmap f Nothing = Nothing
  iDefaultFunctorMaybe .DefaultFunctor.fmap f (Just x) = Just (f x)
  {-# COMPILE AGDA2HS iFunctorMaybe #-}

instance
  iLawfulFunctorMaybe : IsLawfulFunctor Maybe
  iLawfulFunctorMaybe = inst where postulate
    inst : IsLawfulFunctor Maybe
  {-# COMPILE AGDA2HS iLawfulFunctorMaybe laws #-}

instance
  iEqMaybe : ⦃ _ : Eq a ⦄ → Eq (Maybe a)
  iEqMaybe ._==_ Nothing  Nothing  = True
  iEqMaybe ._==_ Nothing  (Just y) = False
  iEqMaybe ._==_ (Just x) Nothing  = False
  iEqMaybe ._==_ (Just x) (Just y) = x == y
  {-# COMPILE AGDA2HS iEqMaybe #-}

  iLawfulEqMaybe : ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ → IsLawfulEq (Maybe a)
  iLawfulEqMaybe .isEquality Nothing Nothing = refl
  iLawfulEqMaybe .isEquality (Just x) (Just y) = mapReflects (cong Just) (λ { refl → refl }) (isEquality x y)

  iArbitraryMaybe : ⦃ _ : Arbitrary a ⦄ → Arbitrary (Maybe a)
  iArbitraryMaybe .arbitrary = frequency ((0 , pure Nothing) ∷ (4 , Just <$> arbitrary) ∷ [])
  iArbitraryMaybe .shrink (Just x) = Nothing ∷ (Just <$> shrink x)
  iArbitraryMaybe .shrink Nothing = []
  {-# COMPILE AGDA2HS iArbitraryMaybe #-}

