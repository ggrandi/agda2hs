module BackgroundTypeClasses where

open import Haskell.Prelude hiding (Eq; _==_; _×_; fst; snd)

-- Pair type
record Pair (A B : Type) : Type where
  field
    fst : A
    snd : B

-- Eq Type class
record Eq (a : Type) : Type where
  infix 4 _==_
  field
    _==_ : a → a → Bool

-- Allow access to the fields of the Eq typeclass
open Eq ⦃...⦄ public

instance
  open Pair
  -- Create an instance for Eq for pairs stating that two pairs are equal iff
  -- they have the same first and second element
  iEqPair : ⦃ Eq a ⦄ → ⦃ Eq b ⦄ → Eq (Pair a b)
  iEqPair ._==_ x y = fst x == fst y && snd x == snd y
