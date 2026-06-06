module MonadTrans where

open import Haskell.Prelude

record MonadTrans {m : Type → Type} (t : (Type → Type) → Type → Type) : Type₁ where
  field
    overlap ⦃ iMonadM ⦄ : Monad m
    overlap ⦃ iMonadTM ⦄ : Monad (t m)
    lift : {a : Type} → m a → t m a

open MonadTrans ⦃ ... ⦄ public

{-# COMPILE AGDA2HS MonadTrans class #-}
