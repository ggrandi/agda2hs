module AnalysisPostulated.LawfulMonoidFun where
{-# FOREIGN AGDA2HS import Test.QuickCheck #-}

open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Haskell.Law.Monoid hiding (iLawfulMonoidFun)

postulate instance iLawfulMonoidFun1 : ⦃ iSemB : Monoid b ⦄ → ⦃ IsLawfulMonoid b ⦄ → IsLawfulMonoid (a → b)

-- This does not translate because it cannot deal with the arbitrary `a`, `b`

postulate instance iLawfulMonoidFun2 : IsLawfulMonoid (Integer → List Integer)

-- This does not translate because there is no way to make a `LawfulEq` for functions
