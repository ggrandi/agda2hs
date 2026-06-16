module MonadTrans where

open import Haskell.Prelude
open import Haskell.Control.Monad

open import Haskell.Law.Monad
open import Haskell.Law.Equality

record MonadTrans {m : Type → Type} (t : (Type → Type) → Type → Type) : Type₁ where
  field
    overlap ⦃ iMonadM ⦄ : Monad m
    overlap ⦃ iMonadTM ⦄ : Monad (t m)
    lift : {a : Type} → m a → t m a

open MonadTrans ⦃ ... ⦄ public

{-# COMPILE AGDA2HS MonadTrans class #-}

record MaybeT (m : Type → Type) (a : Type) : Type where
  no-eta-equality; pattern; constructor MaybeT'
  field
    runMaybeT : m (Maybe a)

open MaybeT public

MaybeT'-of-runMaybeT : (x : MaybeT m a) → MaybeT' (runMaybeT x) ≡ x
MaybeT'-of-runMaybeT (MaybeT' x) = refl
runMaybeT-of-MaybeT' : (x : m (Maybe a)) → runMaybeT {m = m} {a = a} (MaybeT' x) ≡ x
runMaybeT-of-MaybeT' x = refl


{-# COMPILE AGDA2HS MaybeT #-}


instance
  iDefaultFunctorMaybeT : ⦃ _ : Functor m ⦄ → DefaultFunctor (MaybeT m)
  iFunctorMaybeT : ⦃ _ : Functor m ⦄ → Functor (MaybeT m)
  iFunctorMaybeT = record{DefaultFunctor iDefaultFunctorMaybeT}
  {-# COMPILE AGDA2HS iFunctorMaybeT #-}

  iDefaultApplicativeMaybeT : ⦃ _ : Monad m ⦄ → DefaultApplicative (MaybeT m)
  iApplicativeMaybeT : ⦃ _ : Monad m ⦄ → Applicative (MaybeT m)
  iApplicativeMaybeT = record{DefaultApplicative iDefaultApplicativeMaybeT}
  {-# COMPILE AGDA2HS iApplicativeMaybeT #-}

  iDefaultMonadMaybeT : ⦃ _ : Monad m ⦄ → DefaultMonad (MaybeT m)
  iMonadMaybeT : ⦃ _ : Monad m ⦄ → Monad (MaybeT m)
  iMonadMaybeT = record{DefaultMonad iDefaultMonadMaybeT}

  {-# COMPILE AGDA2HS iMonadMaybeT #-}

  iDefaultFunctorMaybeT .DefaultFunctor.fmap f (MaybeT' x) = MaybeT' $ f <$>_ <$> x

  iDefaultMonadMaybeT .DefaultMonad._>>=_ (MaybeT' x) f = 
    MaybeT' $ x >>= maybe (return Nothing) (runMaybeT ∘ f)

  iDefaultApplicativeMaybeT .DefaultApplicative.pure = MaybeT' ∘ return ∘ Just
  iDefaultApplicativeMaybeT {m = m} ⦃ iM ⦄ .DefaultApplicative._<*>_ f x = MaybeT' $
    runMaybeT f >>= (maybe (return Nothing) 
      (λ f → runMaybeT x >>= maybe (return Nothing) 
        (return ∘ Just ∘ f)))


assocMaybeT : ∀{b c} {m} ⦃ iM : Monad m ⦄ ⦃ iLM : IsLawfulMonad m ⦄ (x : MaybeT m b) (g : b → MaybeT m c) → 
  iM ._>>=_ (runMaybeT x) (maybe (return Nothing) (runMaybeT ∘ g)) ≡ runMaybeT (iMonadMaybeT ⦃ iM ⦄ ._>>=_ x g) 
assocMaybeT {b} {c} {m} ⦃ iM ⦄ ⦃ iLM ⦄ (MaybeT' x) g 
  = cong-monad x (λ where 
    Nothing → refl
    (Just x) → refl)

instance
  iPreLawfulMonadMaybeT : ⦃ im : Monad m ⦄ ⦃ ilm : IsLawfulMonad m ⦄ → PreLawfulMonad (MaybeT m)
  iPreLawfulMonadMaybeT .PreLawfulMonad.leftIdentity x k 
    = trans
      (cong MaybeT' (leftIdentity (Just x) (maybe (return Nothing) (runMaybeT ∘ k)))) 
      (MaybeT'-of-runMaybeT _)
  iPreLawfulMonadMaybeT {m = m} .PreLawfulMonad.rightIdentity (MaybeT' x) =
    cong MaybeT' $ begin
    x >>= (maybe (return Nothing) (runMaybeT ∘ return))
    ≡⟨ cong-monad x (λ where
      Nothing → refl
      (Just x) → (runMaybeT-of-MaybeT' {m = m} (return (Just x))) )⟩
    x >>= return
    ≡⟨ rightIdentity x ⟩
    x ∎
  iPreLawfulMonadMaybeT .PreLawfulMonad.associativity (MaybeT' x) f g =
    cong MaybeT' $ sym $ begin 
    ((x >>= maybe (return Nothing) (runMaybeT ∘ f)) >>= maybe (return Nothing) (runMaybeT ∘ g))
    ≡⟨ sym (associativity x (maybe (return Nothing) (runMaybeT ∘ f)) (maybe (return Nothing) (runMaybeT ∘ g))) ⟩
    (x >>= λ x₁ → (maybe (return Nothing) (runMaybeT ∘ f) x₁) >>= (maybe (return Nothing) (runMaybeT ∘ g)))
    ≡⟨ cong-monad x (λ where 
      Nothing → leftIdentity Nothing _
      (Just x) → assocMaybeT (f x) g) ⟩
    (x >>= maybe (return Nothing) (runMaybeT ∘ _>>= g ∘ f)) ∎
  iPreLawfulMonadMaybeT .PreLawfulMonad.def->>->>= ma mb = refl
  iPreLawfulMonadMaybeT .PreLawfulMonad.def-pure-return x = refl
  iPreLawfulMonadMaybeT .PreLawfulMonad.def-fmap->>= f (MaybeT' x) =
    cong MaybeT' (trans (def-fmap->>= (f <$>_) x) (cong-monad x (λ where 
      Nothing  → refl
      (Just x) → refl)))
  iPreLawfulMonadMaybeT {m = m} ⦃ im = im ⦄ .PreLawfulMonad.def-<*>->>= (MaybeT' f) (MaybeT' x) =
    cong MaybeT' $ cong-monad f $ λ where
      Nothing → refl
      (Just f) → cong-monad x $ λ where
        Nothing → refl
        (Just x) → refl


