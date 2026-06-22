module AnalysisPostulated.LawfulFunctorTuple₂ where
{-# FOREIGN AGDA2HS import Test.QuickCheck #-}

open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Haskell.Law.Functor hiding (iLawfulFunctorTuple₂)

postulate instance iLawfulFunctorTuple₂ : IsLawfulFunctor (Integer ×_)
{-# COMPILE AGDA2HS iLawfulFunctorTuple₂ laws #-}

-- does not translate with an arbitrary a as the type

