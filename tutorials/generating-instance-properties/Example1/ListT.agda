module Example1.ListT where

{-# FOREIGN AGDA2HS 
{-# LANGUAGE UndecidableInstances #-}
import Test.QuickCheck.Function (Fun(..))
#-}

import Agda.Builtin.Nat

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Monad
open import Example1.Writer

open import Haskell.Test.QuickCheck

record ListT (m : Type → Type) (a : Type) : Type where
  no-eta-equality; pattern; constructor ListT'
  field
    runListT : m (List a)

open ListT public

{-# COMPILE AGDA2HS ListT newtype #-}

instance
  iEqListT : ⦃ _ : Eq (m (List a)) ⦄ → Eq (ListT m a)
  (iEqListT Eq.== x) y = x .runListT == y .runListT

  {-# COMPILE AGDA2HS iEqListT #-}

  iLawfulEqListT : ⦃ _ : Eq (m (List a)) ⦄ → ⦃ _ : IsLawfulEq (m (List a)) ⦄ → IsLawfulEq (ListT m a)
  iLawfulEqListT .IsLawfulEq.isEquality (ListT' x) (ListT' y) = 
    mapReflects (cong ListT') (λ { refl → refl }) (isEquality x y)

  iShowListT : ⦃ _ : Show (m (List a)) ⦄ → Show (ListT m a)
  iShowListT = record {Show₂ (λ where 
    .Show₂.show -> ("ListT (" ++_) ∘ (_++ ")") ∘ show ∘ runListT)}

  {-# COMPILE AGDA2HS iShowListT #-}

  iDefaultFunctorListT : ⦃ _ : Functor m ⦄ → DefaultFunctor (ListT m)
  iDefaultFunctorListT .DefaultFunctor.fmap f (ListT' x) = ListT' $ (f <$>_) <$> x

  iFunctorListT : ⦃ _ : Functor m ⦄ → Functor (ListT m)
  iFunctorListT = record{DefaultFunctor iDefaultFunctorListT}

  {-# COMPILE AGDA2HS iFunctorListT #-}

  iDefaultApplicativeListT : ⦃ _ : Applicative m ⦄ → DefaultApplicative (ListT m)
  iDefaultApplicativeListT .DefaultApplicative.pure = ListT' ∘ pure ∘ pure
  (iDefaultApplicativeListT DefaultApplicative.<*> ListT' mf) (ListT' mx) = ListT' $ _<*>_ <$> mf <*> mx

  iApplicativeListT : ⦃ _ : Applicative m ⦄ → Applicative (ListT m)
  iApplicativeListT = record{DefaultApplicative iDefaultApplicativeListT}

  {-# COMPILE AGDA2HS iApplicativeListT #-}

  iDefaultMonadListT : ⦃ _ : Monad m ⦄ → DefaultMonad (ListT m)
  (iDefaultMonadListT DefaultMonad.>>= m) k = ListT' $ do 
    a <- runListT m
    b <- mapM {List} (runListT ∘ k) a
    pure (concat b)

  iMonadListT : ⦃ _ : Monad m ⦄ → Monad (ListT m)
  iMonadListT = record{DefaultMonad iDefaultMonadListT}

  {-# COMPILE AGDA2HS iMonadListT #-}

  iPreLawfulMonadListT : PreLawfulMonad (ListT (Writer String))
  iPreLawfulMonadListT = TODO
    where postulate TODO : PreLawfulMonad (ListT (Writer String))

  {-# COMPILE AGDA2HS iPreLawfulMonadListT laws #-}

  iArbitraryListT : ⦃ _ : Arbitrary (m (List a)) ⦄ → Arbitrary (ListT m a)
  iArbitraryListT = record { 
    arbitrary = ListT' <$> arbitrary ; 
    shrink = (ListT' <$>_) ∘ shrink ∘ runListT }

  {-# COMPILE AGDA2HS iArbitraryListT #-}
