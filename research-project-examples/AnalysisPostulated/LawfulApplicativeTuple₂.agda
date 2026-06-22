module AnalysisPostulated.LawfulApplicativeTuple₂ where

{-# FOREIGN AGDA2HS
{-# LANGUAGE ScopedTypeVariables #-}
import Test.QuickCheck
import Text.Show.Functions 
#-}

open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Haskell.Law.Applicative hiding (iLawfulApplicativeTuple₂)

postulate instance iLawfulApplicativeTuple₂ : IsLawfulApplicative (List Integer ×_)
{-# COMPILE AGDA2HS iLawfulApplicativeTuple₂ laws #-}

-- running the generated properties fails without importing Text.Show.Functions

