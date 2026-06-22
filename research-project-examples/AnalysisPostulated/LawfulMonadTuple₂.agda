module AnalysisPostulated.LawfulMonadTuple₂ where

{-# FOREIGN AGDA2HS
{-# LANGUAGE ScopedTypeVariables #-}
import Test.QuickCheck
import Text.Show.Functions 
#-}

open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Haskell.Law.Monad hiding (iLawfulMonadTuple₂)

postulate instance iLawfulMonadTuple₂ : PreLawfulMonad (List Integer ×_)
{-# COMPILE AGDA2HS iLawfulMonadTuple₂ laws #-}

-- running the generated properties fails without importing Text.Show.Functions

