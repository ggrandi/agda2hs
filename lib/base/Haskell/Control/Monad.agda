module Haskell.Control.Monad where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Monad
open import Haskell.Prim.String
open import Haskell.Extra.Erase

guard : {{ MonadFail m }} → (b : Bool) → m (Erase (b ≡ True))
guard True = return (Erased refl)
guard False = fail "Guard was not True"

-- ap                :: (Monad m) => m (a -> b) -> m a -> m b
-- ap m1 m2          = do { x1 <- m1; x2 <- m2; return (x1 x2) }

ap : ⦃ _ : Monad m ⦄ → m (a → b) → m a → m b
ap m1 m2 = do
  x1 <- m1
  x2 <- m2
  return (x1 x2)

-- | Promote a function to a monad.
-- This is equivalent to 'fmap' but specialised to Monads.
liftM  : ⦃ _ : Monad m ⦄ → (a -> b) -> m a -> m b
liftM f x = do 
  x <- x
  return (f x)
