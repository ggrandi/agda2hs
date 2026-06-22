module AnalysisPostulated.LawfulOrdNat where
{-# FOREIGN AGDA2HS import Test.QuickCheck #-}

open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Haskell.Law.Ord hiding (iLawfulOrdNat)

postulate instance iLawfulOrdNat : IsLawfulOrd Nat
{-# COMPILE AGDA2HS iLawfulOrdNat laws #-}

-- This does not translate because `transitivity` has a precondition check
