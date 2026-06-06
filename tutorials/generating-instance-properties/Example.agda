module Example where

open import Haskell.Prim
open import Haskell.Prelude hiding (mempty; mappend)
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Level)

record Foo (a : Type) : Type where
  field
    foo : a

open Foo ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Foo class #-}

record Bar (a : Type) : Type₁ where
  field
    bar : ∀ {b : Type} → ⦃ _ : Foo b ⦄ → (x : b) → x ≡ foo

postulate TODO : {α : Type} → α

instance
  iFooNat : Foo Nat
  iFooNat .Foo.foo = 100

  {-# COMPILE AGDA2HS iFooNat #-}

  iBarNat : Bar Nat
  iBarNat .Bar.bar x = TODO

  {-# COMPILE AGDA2HS iBarNat laws #-}


