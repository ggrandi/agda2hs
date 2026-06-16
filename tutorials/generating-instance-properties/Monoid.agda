module Monoid where

open import Haskell.Prim using (the)
open import Haskell.Prelude
open import Haskell.Law.Monoid
open import Haskell.Law.Equality
open import Haskell.Law.Eq
open import Agda.Builtin.Nat using (Nat)
open import Haskell.Extra.Dec

data Add : Type where
  Add' : (x : Nat) → Add

{-# COMPILE AGDA2HS Add newtype #-}

postulate
  TODO : {α : Type} → α

instance
  iEqAdd : Eq Add
  (iEqAdd Eq.== Add' x) (Add' y) = x == y

  {-# COMPILE AGDA2HS iEqAdd #-}
  iLawfulEqAdd : IsLawfulEq Add
  iLawfulEqAdd .IsLawfulEq.isEquality (Add' x) (Add' y) = mapReflects (cong Add') (λ { refl → refl }) (isEquality x y)

  iSemigroupAdd : Semigroup Add
  (iSemigroupAdd Semigroup.<> Add' x) (Add' y) = Add' $ x + y

  {-# COMPILE AGDA2HS iSemigroupAdd #-}

  iMonoidAdd : Monoid Add
  iMonoidAdd = record {DefaultMonoid (λ where .DefaultMonoid.mempty → Add' 0) }

  {-# COMPILE AGDA2HS iMonoidAdd #-}

  iLawfulSemigroupAdd : IsLawfulSemigroup Add
  iLawfulSemigroupAdd .associativity x y z = TODO

  {-# COMPILE AGDA2HS iLawfulSemigroupAdd laws #-}

  iLawfulMonoidAdd : IsLawfulMonoid Add
  iLawfulMonoidAdd .IsLawfulMonoid.rightIdentity (Add' x) = cong Add' $ aux x where
    aux : (x : Nat) → x + 0 ≡ x
    aux zero = refl
    aux (suc x) = cong suc $ aux x
  iLawfulMonoidAdd .IsLawfulMonoid.leftIdentity (Add' x) = refl
  iLawfulMonoidAdd .IsLawfulMonoid.concatenation [] = refl
  iLawfulMonoidAdd .IsLawfulMonoid.concatenation (x ∷ xs) = cong (x <>_) $ concatenation xs

  {-# COMPILE AGDA2HS iLawfulMonoidAdd laws #-}

