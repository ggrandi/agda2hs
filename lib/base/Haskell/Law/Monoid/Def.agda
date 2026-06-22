module Haskell.Law.Monoid.Def where

open import Haskell.Prim
open import Haskell.Prim.Tuple

open import Haskell.Prim.Foldable
open import Haskell.Prim.Monoid

open import Haskell.Law.Semigroup.Def
open import Haskell.Law.Extensionality
open import Haskell.Law.Equality

record IsLawfulMonoid (a : Type) ⦃ iMonoidA : Monoid a ⦄ : Type₁ where
  field
    overlap ⦃ super ⦄ : IsLawfulSemigroup a

    -- Right identity: x <> mempty = x
    rightIdentity : (x : a) → x <> mempty ≡ x

    -- Left identity: mempty <> x = x
    leftIdentity : (x : a) → mempty <> x ≡ x

    -- Concatenation: mconcat = foldr (<>) mempty
    concatenation : (xs : List a) → mconcat xs ≡ foldr _<>_ mempty xs

open IsLawfulMonoid ⦃ ... ⦄ public

instance
  iLawfulMonoidFun : ⦃ iSemB : Monoid b ⦄ → ⦃ IsLawfulMonoid b ⦄ → IsLawfulMonoid (a → b)
  iLawfulMonoidFun .IsLawfulMonoid.rightIdentity f = ext λ { x → rightIdentity (f x) }
  iLawfulMonoidFun .IsLawfulMonoid.leftIdentity f = ext λ { x → leftIdentity (f x) }
  iLawfulMonoidFun .IsLawfulMonoid.concatenation [] = refl
  iLawfulMonoidFun .IsLawfulMonoid.concatenation (f ∷ fs) = cong (f <>_) $ iLawfulMonoidFun .IsLawfulMonoid.concatenation fs

  iLawfulMonoidUnit : IsLawfulMonoid ⊤
  iLawfulMonoidUnit .IsLawfulMonoid.rightIdentity x = refl
  iLawfulMonoidUnit .IsLawfulMonoid.leftIdentity x = refl
  iLawfulMonoidUnit .IsLawfulMonoid.concatenation [] = refl
  iLawfulMonoidUnit .IsLawfulMonoid.concatenation (x ∷ xs) = cong (x <>_) $ concatenation xs

  iLawfulMonoidTuple₂ : ⦃ iSemA : Monoid a ⦄ ⦃ iSemB : Monoid b ⦄
                      → ⦃ IsLawfulMonoid a ⦄ → ⦃ IsLawfulMonoid b ⦄
                      → IsLawfulMonoid (a × b)
  iLawfulMonoidTuple₂ .IsLawfulMonoid.rightIdentity x = cong₂ _,_ (rightIdentity _) (rightIdentity _)
  iLawfulMonoidTuple₂ .IsLawfulMonoid.leftIdentity x = cong₂ _,_ (leftIdentity _) (leftIdentity _)
  iLawfulMonoidTuple₂ .IsLawfulMonoid.concatenation [] = refl
  iLawfulMonoidTuple₂ .IsLawfulMonoid.concatenation (x ∷ xs) = cong (x <>_) $ concatenation xs

  postulate iLawfulMonoidTuple₃ : ⦃ iSemA : Monoid a ⦄ ⦃ iSemB : Monoid b ⦄ ⦃ iSemC : Monoid c ⦄
                      → ⦃ IsLawfulMonoid a ⦄ → ⦃ IsLawfulMonoid b ⦄ → ⦃ IsLawfulMonoid c ⦄
                      → IsLawfulMonoid (a × b × c)

