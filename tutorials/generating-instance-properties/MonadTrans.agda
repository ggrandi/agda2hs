module MonadTrans where

open import Haskell.Prelude

record MonadTrans {m : Type → Type} (t : (Type → Type) → Type → Type) ⦃ _ : Monad (t m) ⦄ : Type₁ where
  field
    lift : {a : Type} {m : Type → Type} ⦃ _ : Monad m ⦄ → m a → t m a

open MonadTrans ⦃ ... ⦄ public

{-# COMPILE AGDA2HS MonadTrans class #-}
