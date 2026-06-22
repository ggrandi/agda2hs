module Vector where

open import Haskell.Prelude
open import Haskell.Extra.Refinement
open import Haskell.Extra.Erase
open import Haskell.Law.Equality

data Vec (a : Type) : (@0 n : Nat) → Type where
  Nil : Vec a 0
  Cons : {@0 n : Nat} → a → Vec a n → Vec a (suc n)
{-# COMPILE AGDA2HS Vec #-}

mapV : {a b : Type} {@0 n : Nat} (f : a → b) → Vec a n → Vec b n
mapV f Nil = Nil
mapV f (Cons x xs) = Cons (f x) (mapV f xs)
{-# COMPILE AGDA2HS mapV #-}

tailV : {a : Type} {@0 n : Nat} → Vec a (suc n) → Vec a n
tailV (Cons x xs) = xs
{-# COMPILE AGDA2HS tailV #-}

len : {a : Type} {@0 n : Nat} → Vec a n → Singleton n
len Nil = sing 0
len (Cons _ xs) = (1 + len xs .value) ⟨ cong suc (len xs .proof) ⟩
{-# COMPILE AGDA2HS len #-}

instance
  iEqVec : {@0 n : Nat} ⦃ _ : Eq a ⦄ → Eq (Vec a n)
  iEqVec .Eq._==_ Nil Nil = True
  iEqVec .Eq._==_ (Cons x xs) (Cons y ys) = x == y && xs == ys
  iEqVec .Eq._==_ _ _ = False

  {-# COMPILE AGDA2HS iEqVec #-}
