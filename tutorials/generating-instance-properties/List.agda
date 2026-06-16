module List where

open import Haskell.Prim
open import Haskell.Prelude
open import Haskell.Law.Applicative
open import Haskell.Law.Ord.Def
open import Haskell.Extra.Refinement

record Collection (C : Type → Type) (A : Type) : Type₁ where
  field
    empty     : C A
    add       : (x : A) (xs : C A) → C A
    removeAll : (x : C A) (xs : C A) → C A
    contains  : (x : A) (xs : C A) → Bool
    size      : (xs : C A) → Nat

  singleton : A → C A
  singleton x = add x empty

open Collection ⦃...⦄ public

record IsLawfulCollection (C : Type → Type) (A : Type)
  ⦃ iColCA : Collection C A ⦄ : Type₁ where
  field
    size-empty : size (the (C A) empty) ≡ 0
    size-add   : (xs : C A) (x : A) → size (add x xs) ≡ suc (size xs)

    contains-singleton : (x : A) → contains x (singleton x) ≡ True
    contains-add : (y x : A) (xs : C A) → contains y xs ≡ True → contains x (singleton x) ≡ True
