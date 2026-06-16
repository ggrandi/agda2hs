module Alternative where

open import Haskell.Prim using (the)
open import Haskell.Prelude
open import Haskell.Law.Applicative
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Agda.Builtin.Nat using (Nat)
open import Haskell.Extra.Dec

record Alternative (f : Type → Type) : Type₁ where
  infixl 3 _<|>_
  field
    overlap ⦃ super ⦄ : Applicative f
    empty  : f a
    _<|>_ : f a → f a → f a

open Alternative ⦃...⦄ public
{-# COMPILE AGDA2HS Alternative existing-class #-}

record IsLawfulAlternative (f : Type → Type) ⦃ iAltF : Alternative f ⦄ : Type₁ where
  field
    overlap ⦃ super ⦄ : IsLawfulApplicative f
    map-empty : {a b : Type} (g : a → b) → (g <$> empty) ≡ the (f b) empty
    seq-empty : {a b : Type} (g : f (a → b)) → (g <*> empty) ≡ empty
    empty-seq : {a b : Type} (g : f a) → (empty <*> g) ≡ the (f b) empty
    or-empty : {a : Type} (x : f a) → (x <|> empty) ≡ x
    empty-or : {a : Type} (x : f a) → (empty <|> x) ≡ x
    or-assoc : {a : Type} (x y z : f a) → (x <|> (y <|> z)) ≡ ((x <|> y) <|> z)
    map-or : {a : Type} (g : a → b) (x y : f a) → (g <$> (x <|> y)) ≡ ((g <$> x) <|> (g <$> y))

open IsLawfulAlternative ⦃...⦄ public

postulate
  TODO : ∀{a} {A : Type a} → A

instance
  open Alternative

  iAlternativeMaybe : Alternative Maybe
  empty iAlternativeMaybe = Nothing
  _<|>_ iAlternativeMaybe Nothing y = y
  _<|>_ iAlternativeMaybe (Just x) y = Just x

  {-# COMPILE AGDA2HS iAlternativeMaybe #-}

  iAlternativeList : Alternative List
  empty iAlternativeList = []
  _<|>_ iAlternativeList x y = x ++ y

  {-# COMPILE AGDA2HS iAlternativeList #-}

  open IsLawfulAlternative

  iLawfulAlternativeMaybe : IsLawfulAlternative Maybe

  {-# COMPILE AGDA2HS iLawfulAlternativeMaybe laws #-}

  -- iLawfulAlternativeMaybe = TODO
  map-empty iLawfulAlternativeMaybe g = refl
  seq-empty iLawfulAlternativeMaybe Nothing = refl
  seq-empty iLawfulAlternativeMaybe (Just x) = refl
  empty-seq iLawfulAlternativeMaybe = λ { Nothing → refl ; (Just x) → refl }
  or-empty iLawfulAlternativeMaybe Nothing = refl
  or-empty iLawfulAlternativeMaybe (Just x) = refl
  empty-or iLawfulAlternativeMaybe Nothing = refl
  empty-or iLawfulAlternativeMaybe (Just x) = refl
  or-assoc iLawfulAlternativeMaybe Nothing y z = refl
  or-assoc iLawfulAlternativeMaybe (Just x) y z = refl
  map-or iLawfulAlternativeMaybe g Nothing y = refl
  map-or iLawfulAlternativeMaybe g (Just x) y = refl

  iLawfulAlternativeList : IsLawfulAlternative List
  iLawfulAlternativeList .map-empty g = refl
  iLawfulAlternativeList .seq-empty [] = refl
  iLawfulAlternativeList .seq-empty (_ ∷ g) = iLawfulAlternativeList .seq-empty g
  iLawfulAlternativeList .empty-seq g = refl
  iLawfulAlternativeList .or-empty [] = refl
  iLawfulAlternativeList .or-empty (x ∷ xs) = cong (_ ∷_) (iLawfulAlternativeList .or-empty xs)
  iLawfulAlternativeList .empty-or x = refl
  iLawfulAlternativeList .or-assoc [] ys zs = refl
  iLawfulAlternativeList .or-assoc (x ∷ xs) ys zs = cong (_ ∷_) (iLawfulAlternativeList .or-assoc xs ys zs)
  iLawfulAlternativeList .map-or g [] ys = refl
  iLawfulAlternativeList .map-or g (x ∷ xs) ys = cong (_ ∷_) (iLawfulAlternativeList .map-or g xs ys)

  {-# COMPILE AGDA2HS iLawfulAlternativeList laws #-}

