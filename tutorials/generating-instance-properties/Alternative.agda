module Alternative where

open import Haskell.Prim using (the)
open import Haskell.Prelude
open import Haskell.Law.Applicative

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
    -- map-empty : {a b : Type} (g : a → b) → (g <$> empty) ≡ empty
    -- seq-empty : {a b : Type} (g : f (a → b)) → (g <*> empty) ≡ empty
    empty-seq : {a b : Type} (g : f a) → (empty <*> g) ≡ empty {f} {f b}
    or-empty : {a : Type} (x : f a) → (x <|> empty) ≡ x
    -- empty-or : {a : Type} (x : f a) → (empty <|> x) ≡ x
    -- or-assoc : {a : Type} (x y z : f a) → (x <|> (y <|> z)) ≡ ((x <|> y) <|> z)
    -- map-or : {a : Type} (g : a → b) (x y : f a) → (g <$> (x <|> y)) ≡ ((g <$> x) <|> (g <$> y))

-- {-# COMPILE AGDA2HS IsLawfulAlternative #-}

postulate
  TODO : ∀{a} {A : Type a} → A

instance
  open Alternative

  iAlternativeMaybe : Alternative Maybe
  empty iAlternativeMaybe = Nothing
  _<|>_ iAlternativeMaybe Nothing y = y
  _<|>_ iAlternativeMaybe (Just x) y = Just x


  open IsLawfulAlternative

  iLawfulAlternativeMaybe : IsLawfulAlternative Maybe
  iLawfulAlternativeMaybe = TODO
  -- map-empty iLawfulAlternativeMaybe g = refl
  -- seq-empty iLawfulAlternativeMaybe {a} {b} Nothing = refl
  -- seq-empty iLawfulAlternativeMaybe {a} {b} (Just x) = refl
  -- empty-seq iLawfulAlternativeMaybe Nothing = refl
  -- empty-seq iLawfulAlternativeMaybe (Just x) = refl
  -- or-empty iLawfulAlternativeMaybe Nothing = refl
  -- or-empty iLawfulAlternativeMaybe (Just x) = refl
  -- empty-or iLawfulAlternativeMaybe Nothing = refl
  -- empty-or iLawfulAlternativeMaybe (Just x) = refl
  -- or-assoc iLawfulAlternativeMaybe Nothing y z = refl
  -- or-assoc iLawfulAlternativeMaybe (Just x) y z = refl
  -- map-or iLawfulAlternativeMaybe g Nothing y = refl
  -- map-or iLawfulAlternativeMaybe g (Just x) y = refl

{-# COMPILE AGDA2HS iAlternativeMaybe #-}
{-# COMPILE AGDA2HS iLawfulAlternativeMaybe laws #-}
