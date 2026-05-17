module MonadPlus where

open import Alternative
open import Haskell.Prim
open import Haskell.Prelude hiding (mempty; mappend)

record MonadPlus (m : Type → Type) : Type₁ where
  field
    overlap ⦃ super-monad ⦄ : Monad m 
    overlap ⦃ super-alt ⦄ : Alternative m 

  mempty : m a
  mempty = empty

  mplus : m a → m a → m a
  mplus = _<|>_


open MonadPlus ⦃...⦄ public
{-# COMPILE AGDA2HS MonadPlus class #-}

record IsLawfulMonadPlus (m : Type → Type) ⦃ _ : MonadPlus m ⦄ : Type₁ where
  field
    overlap ⦃ super ⦄ : IsLawfulAlternative m
    left-zero : ∀(k : a → m b) → (mempty >>= k) ≡ mempty
    left-distribution : ∀(x y : m a) (k : a → m b) → (mplus x y >>= k) ≡ mplus (x >>= k) (y >>= k)



