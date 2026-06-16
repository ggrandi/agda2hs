module MonadPlus where

open import Alternative hiding (TODO)
open import Haskell.Prim
open import Haskell.Prelude hiding (mempty; mappend)
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.List
open import Agda.Builtin.Nat using (Nat)

record MonadPlus (m : Type → Type) : Type₁ where
  field
    overlap ⦃ super-monad ⦄ : Monad m
    overlap ⦃ super-alt ⦄ : Alternative m

open MonadPlus ⦃...⦄ public
{-# COMPILE AGDA2HS MonadPlus existing-class #-}

record IsLawfulMonadPlus (m : Type → Type) ⦃ _ : MonadPlus m ⦄ : Type₁ where
  field
    overlap ⦃ super ⦄ : IsLawfulAlternative m
    left-zero : ∀{a b : Type} (k : a → m b) → (_>>=_ {m} empty k) ≡ the (m b) empty
    left-distribution : ∀{a b : Type} (x y : m a) (k : a → m b) → (_>>=_ {m} (x <|> y) k) ≡ _<|>_ {m} (x >>= k) (y >>= k)

postulate
  TODO : ∀{a} {A : Type a} → A

instance
  iMonadPlusList : MonadPlus List
  iMonadPlusList = record {}

  {-# COMPILE AGDA2HS iMonadPlusList #-}

  iLawfulMonadPlusList : IsLawfulMonadPlus List
  iLawfulMonadPlusList .IsLawfulMonadPlus.left-zero k = refl
  iLawfulMonadPlusList .IsLawfulMonadPlus.left-distribution [] ys k = refl
  iLawfulMonadPlusList .IsLawfulMonadPlus.left-distribution (x ∷ xs) ys k = begin 
    k x ++ (xs <|> ys) >>= k
      ≡⟨ cong (_ ++_) (iLawfulMonadPlusList .IsLawfulMonadPlus.left-distribution xs ys k ) ⟩
    k x ++ (xs >>= k ++ ys >>= k)
      ≡⟨ sym (++-assoc (k x) _ _) ⟩
    (k x ++ xs >>= k) ++ (ys >>= k)
    ∎

  {-# COMPILE AGDA2HS iLawfulMonadPlusList laws #-}

