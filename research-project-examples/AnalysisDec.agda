module AnalysisDec where

open import Haskell.Prelude
open import Haskell.Prim using (the; it)
open import Haskell.Extra.Dec
open import Haskell.Extra.Dec.Instances
open import Haskell.Extra.Refinement
open import Haskell.Law.Ord
open import Haskell.Law.Eq
open import Haskell.Data.List
open import Haskell.Data.Maybe

data IsAscending {a : Type} ⦃ iOrdA : Ord a ⦄ : List a → Type where
  instance
    Empty : IsAscending []
    OneElem : {x : a} →  IsAscending (x ∷ [])
    ManyElem : {x y : a} {xs : List a}
        → ⦃ IsTrue (x <= y) ⦄
        → ⦃ IsAscending (y ∷ xs) ⦄
        → IsAscending (x ∷ y ∷ xs)


instance
  decIsAscending : {a : Type} ⦃ _ : Ord a ⦄ {xs : List a} → Dec (IsAscending xs)
  decIsAscending {xs = []} = True ⟨⟩
  decIsAscending {xs = _ ∷ []} = True ⟨⟩
  decIsAscending {xs = x ∷ y ∷ xs} = mapDec
    (λ { (h , h') → ManyElem ⦃ _ ⦄ ⦃ h ⦄ ⦃ h' ⦄ })
    (λ { (ManyElem ⦃ h ⦄ ⦃ h' ⦄) → h , h' })
    (iDecPair {IsTrue (x <= y)} {IsAscending (y ∷ xs)})

  {-# COMPILE AGDA2HS decIsAscending #-}

record ExtractSorted (cont : Type → Type) : Type₁ where
  field
    extractSorted : ⦃ _ : Ord a ⦄ → cont a → List a

{-# COMPILE AGDA2HS ExtractSorted class #-}

open ExtractSorted ⦃ ... ⦄ public

instance
  iExtractSortedList : ExtractSorted List
  iExtractSortedList = record { extractSorted = sort }
  {-# COMPILE AGDA2HS iExtractSortedList #-}

record IsLawfulExtractSorted (cont : Type → Type) ⦃ _ : ExtractSorted cont ⦄ : Type₁ where
  field
    IsAscending-extractSorted : ∀{a} ⦃ _ : Ord a ⦄ ⦃ _ : IsLawfulOrd a ⦄ (xs : cont a)
      → IsAscending (extractSorted xs)

open IsLawfulExtractSorted ⦃ ... ⦄ public

postulate instance
  iLawfulExtractSortedList : IsLawfulExtractSorted List
{-# COMPILE AGDA2HS iLawfulExtractSortedList laws #-}
