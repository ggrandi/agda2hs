module Example1.Writer where

-- {-# FOREIGN AGDA2HS {-# LANGUAGE UndecidableInstances #-} #-}
{-# FOREIGN AGDA2HS 
import Test.QuickCheck (Arbitrary (..))
import Data.Functor (($>))
#-}

open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Haskell.Law.Equality

-- newtype Writer m a = Writer {runWriter :: m [a]}
record Writer (w a : Type) : Type where
  no-eta-equality; pattern; constructor Writer'
  field
    runWriter : w × a

open Writer public

{-# COMPILE AGDA2HS Writer newtype deriving (Show) #-}

variable
  w : Type

tell : w → Writer w ⊤
tell = Writer' ∘ (_, tt)

{-# COMPILE AGDA2HS tell #-}

instance
  iEqWriter : ⦃ _ : Eq w ⦄ → ⦃ _ : Eq a ⦄ → Eq (Writer w a)
  iEqWriter .Eq._==_ (Writer' x) (Writer' y) = x == y

  {-# COMPILE AGDA2HS iEqWriter #-}

  iLawfulEqWriter : ⦃ _ : Eq w ⦄ → ⦃ _ : IsLawfulEq w ⦄ → ⦃ _ : Eq a ⦄ → ⦃ _ : IsLawfulEq a ⦄ 
    → IsLawfulEq (Writer w a)
  iLawfulEqWriter .IsLawfulEq.isEquality (Writer' x) (Writer' y) = 
    mapReflects (cong Writer') (λ { refl → refl }) (isEquality x y)

  iDefaultFunctorWriter : DefaultFunctor (Writer w)
  iDefaultFunctorWriter .DefaultFunctor.fmap f (Writer' x) = Writer' $ f <$> x

  iFunctorWriter : Functor (Writer w)
  iFunctorWriter = record{DefaultFunctor iDefaultFunctorWriter}

  {-# COMPILE AGDA2HS iFunctorWriter #-}

  iDefaultApplicativeWriter : ⦃ _ : Monoid w ⦄ → DefaultApplicative (Writer w)
  iDefaultApplicativeWriter .DefaultApplicative.pure = Writer' ∘ pure
  iDefaultApplicativeWriter .DefaultApplicative._<*>_ (Writer' mf) (Writer' mx) = Writer' $ mf <*> mx
  
  iApplicativeWriter : ⦃ _ : Monoid w ⦄ → Applicative (Writer w)
  iApplicativeWriter = record{DefaultApplicative iDefaultApplicativeWriter}
  
  {-# COMPILE AGDA2HS iApplicativeWriter #-}
  
  iDefaultMonadWriter : ⦃ _ : Monoid w ⦄ → DefaultMonad (Writer w)
  (iDefaultMonadWriter DefaultMonad.>>= Writer' x) k = Writer' $ x >>= (runWriter ∘ k)

  iMonadWriter : ⦃ _ : Monoid w ⦄ → Monad (Writer w)
  iMonadWriter = record{DefaultMonad iDefaultMonadWriter}

  {-# COMPILE AGDA2HS iMonadWriter #-}


{-# FOREIGN AGDA2HS

instance (Arbitrary w, Arbitrary a) => Arbitrary (Writer w a) where
  arbitrary = liftA2 (($>) . tell) arbitrary arbitrary

  shrink x =
    let (w, a) = runWriter x
     in liftA2 (($>) . tell) (shrink w) (shrink a)

#-}
