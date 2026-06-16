module Hello where

open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement

dec : (@0 a : Type) ⦃ _ : Dec a ⦄ → Dec a
dec _ ⦃ x ⦄ = x
{-# COMPILE AGDA2HS dec transparent #-}

fun : (x : List Nat) → Bool
fun x = if' (IsTrue (length x == 1)) then False else True

{-# COMPILE AGDA2HS fun #-}
