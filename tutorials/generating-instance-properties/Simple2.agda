module Simple2 where

open import Haskell.Prim using (the)
open import Haskell.Prelude
open import Haskell.Law.Applicative
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Agda.Builtin.Nat using (Nat)

postulate
  TODO : ∀{a} {A : Type a} → A

record Trivial (a : Type) : Type₁ where
  field
    trivial : (x y : a) → x ≡ y

instance
  iTrivial : Trivial Nat
  iTrivial = TODO

{-# COMPILE AGDA2HS iTrivial laws #-}

