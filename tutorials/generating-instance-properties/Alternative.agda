module Alternative where

open import Haskell.Prim using (the)
open import Haskell.Prelude
open import Haskell.Law.Applicative

record Alternative (f : Type → Type) : Type₁ where
  infixl 3 _<|>_
  field
    empty  : f a
    _<|>_ : f a → f a → f a
    overlap ⦃ super ⦄ : Applicative f

open Alternative ⦃...⦄ public
{-# COMPILE AGDA2HS Alternative existing-class #-}

record IsLawfulAlternative (f : Type → Type) ⦃ iAltF : Alternative f ⦄ : Type₁ where
  field
    map-empty : {a b : Type} (g : a → b) → (g <$> empty) ≡ empty
    seq-empty : {a b : Type} (g : f (a → b)) → (g <*> empty) ≡ empty
    empty-seq : {a b : Type} (g : f a) → (empty <*> g) ≡ the (f b) empty
    -- or-empty : {a : Type} (x : f a) → (x <|> empty) ≡ x
    -- empty-or : {a : Type} (x : f a) → (empty <|> x) ≡ x
    -- or-assoc : {a : Type} (x y z : f a) → (x <|> (y <|> z)) ≡ ((x <|> y) <|> z)
    -- map-or : {a : Type} (g : a → b) (x y : f a) → (g <$> (x <|> y)) ≡ ((g <$> x) <|> (g <$> y))

-- {-# COMPILE AGDA2HS IsLawfulAlternative #-}

instance
  open Alternative

  iAlternativeMaybe : Alternative Maybe
  iAlternativeMaybe .empty = Nothing
  (iAlternativeMaybe <|> Nothing) y = y
  (iAlternativeMaybe <|> Just x) y = Just x
  iAlternativeMaybe .super = iApplicativeMaybe


  open IsLawfulAlternative

  iLawfulAlternativeMaybe : IsLawfulAlternative Maybe
  iLawfulAlternativeMaybe .IsLawfulAlternative.map-empty g = refl
  iLawfulAlternativeMaybe .seq-empty Nothing = refl
  iLawfulAlternativeMaybe .seq-empty (Just x) = refl
  iLawfulAlternativeMaybe .empty-seq g = refl
  -- iLawfulAlternativeMaybe .or-empty Nothing = refl
  -- iLawfulAlternativeMaybe .or-empty (Just x) = refl
  -- iLawfulAlternativeMaybe .empty-or Nothing = refl
  -- iLawfulAlternativeMaybe .empty-or (Just x) = refl
  -- iLawfulAlternativeMaybe .or-assoc Nothing y z = refl
  -- iLawfulAlternativeMaybe .or-assoc (Just x) y z = refl
  -- iLawfulAlternativeMaybe .map-or {b} {a} g Nothing y = refl
  -- iLawfulAlternativeMaybe .map-or {b} {a} g (Just x) y = refl

{-# COMPILE AGDA2HS iAlternativeMaybe #-}
{-# COMPILE AGDA2HS iLawfulAlternativeMaybe laws #-}
