module Simple where

open import Haskell.Prim using (the)
open import Haskell.Prelude
open import Haskell.Law.Applicative
open import Haskell.Extra.Dec
open import Haskell.Law.Eq

record Foo (a : Type) : Type₁ where
  field
    bar       : a
    baz       : a
    bar2baz   : a -> a

open Foo ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Foo class #-}

instance
  iFooNat : Foo Nat
  iFooNat .bar = 0
  iFooNat .baz = 1
  iFooNat .bar2baz = suc

{-# COMPILE AGDA2HS iFooNat #-}

postulate
  TODO : ∀{a} {A : Type a} → A

record IsLawfulFoo (a : Type) ⦃ _ : Foo a ⦄ : Type₁ where
  field
    bar2baz-of-bar : bar2baz (the a bar) ≡ baz


instance
  iLawfulFooNat : IsLawfulFoo Nat
  iLawfulFooNat = TODO

{-# COMPILE AGDA2HS iLawfulFooNat laws #-}
