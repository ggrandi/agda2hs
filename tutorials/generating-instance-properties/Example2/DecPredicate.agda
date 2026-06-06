{-# OPTIONS --experimental-lazy-instances #-}
module Example2.DecPredicate where

open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Extra.Dec.Instances
open import Haskell.Extra.Refinement
open import Haskell.Law.Ord
open import Haskell.Data.List

data IsAscending {a : Type} ⦃ iOrdA : Ord a ⦄ : List a → Type where
    Empty : IsAscending []
    OneElem : {x : a} →  IsAscending (x ∷ [])
    ManyElem : {x y : a} {xs : List a}
        → ⦃ IsAscending (y ∷ xs) ⦄
        → ⦃ IsTrue (x <= y) ⦄
        → IsAscending (x ∷ y ∷ xs)

instance
  decIsAscending : {a : Type} ⦃ _ : Ord a ⦄ {xs : List a} → Dec (IsAscending xs)
  decIsAscending {xs = []} = True ⟨ Empty ⟩
  decIsAscending {xs = x ∷ []} = True ⟨ OneElem ⟩
  decIsAscending {xs = x ∷ y ∷ xs} = mapDec' (IsTrue (x <= y) × IsAscending (y ∷ xs))
    (λ { (h' , h) → ManyElem ⦃ _ ⦄ ⦃ h ⦄ ⦃ h' ⦄ }) 
    (λ { (ManyElem ⦃ h ⦄ ⦃ h' ⦄) → h' , h }) 

  {-# COMPILE AGDA2HS decIsAscending #-}

record Sortable (cont : Type → Type) : Type₁ where
  field
    ascendingList : ⦃ _ : Ord a ⦄ → cont a → List a

{-# COMPILE AGDA2HS Sortable class #-}

open Sortable ⦃ ... ⦄ public

instance
  iSortableList : Sortable List
  iSortableList = record { ascendingList = sort }
  {-# COMPILE AGDA2HS iSortableList #-}

record IsLawfulSortable (cont : Type → Type) ⦃ _ : Sortable cont ⦄ : Type₁ where
  field
    IsAscending-ascendingList : ∀{a} ⦃ _ : Ord a ⦄ ⦃ _ : IsLawfulOrd a ⦄ (xs : cont a) 
      → IsAscending (ascendingList xs)

open IsLawfulSortable ⦃ ... ⦄ public

instance 
  iLawfulSortableList : IsLawfulSortable List
  iLawfulSortableList .IsAscending-ascendingList = prf where postulate 
    prf : ∀{a} ⦃ _ : Ord a ⦄ (xs : List a) → IsAscending (Sortable.ascendingList iSortableList xs)
  {-# COMPILE AGDA2HS iLawfulSortableList laws #-}

fun : (xs : List (List Nat)) → Bool
fun xs = decide (IsTrue (length xs == 1)) .value

{-# COMPILE AGDA2HS fun #-}
