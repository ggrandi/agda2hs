module Haskell.Extra.Dec.Instances where

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement
open import Haskell.Law.Nat
open import Haskell.Data.Maybe


instance
  decLE : {m n : Nat} → Dec (m ≤ n)
  decLE {m} {n} = (m <= n) ⟨ aux m n ⟩ where
    ≤-if-<= : {m n : Nat} → (m <= n) ≡ True → m ≤ n
    ≤-if-<= {zero}  {n}     _ = z≤n
    ≤-if-<= {suc m} {suc n} h = s≤s (≤-if-<= h)

    not-≤-if-not-<= : {m n : Nat} → (m <= n) ≡ False → m ≤ n → ⊥
    not-≤-if-not-<= {zero}  {zero}  h _        = exFalso {zero <= zero} refl h
    not-≤-if-not-<= {zero}  {suc n} h _        = exFalso {zero <= suc n} refl h
    not-≤-if-not-<= {suc m} {suc n} h (s≤s h') = not-≤-if-not-<= h h'

    aux : (m n : Nat) → Reflects (m ≤ n) (m <= n)
    aux m n with m <= n in h
    ... | True = ≤-if-<= h
    ... | False = not-≤-if-not-<= h

  {-# COMPILE AGDA2HS decLE inline #-}

  decIsJust : {x : Maybe a} → Dec (IsJust x)
  decIsJust {x = x} = (isJust x) ⟨ aux x ⟩ where
    aux : (x : Maybe a) → Reflects (IsJust x) (isJust x)
    aux Nothing = id
    aux (Just _) = tt

  {-# COMPILE AGDA2HS decIsJust inline #-}

  decAll : {A : Type} {P : A → Type} ⦃ _ : ∀{x} → Dec (P x) ⦄ {xs : List A} → Dec (All P xs)
  decAll {P = P} {xs = xs} = (all (λ x → decide (P x) .value) xs) ⟨ All-reflects-all P xs ⟩ where
    @0 All-reflects-all : {A : Type} (P : A → Type) ⦃ _ : ∀{x} → Dec (P x) ⦄ (xs : List A)
      → Reflects (All P xs) (all (λ x → decide (P x) .value) xs)
    All-reflects-all P [] = allNil
    All-reflects-all P (x ∷ xs) = mapReflects
      {P x × All P xs}
      {All P (x ∷ xs)}
      (λ { (i , is) → allCons ⦃ i ⦄ ⦃ is ⦄ })
      (λ { (allCons ⦃ i ⦄ ⦃ is ⦄ ) → i , is })
      (×-reflects-&& (reflects-decide (P x)) (All-reflects-all P xs))

  {-# COMPILE AGDA2HS decAll inline #-}

  decAny : {A : Type} {P : A → Type} ⦃ _ : ∀{x} → Dec (P x) ⦄ {xs : List A} → Dec (Any P xs)
  decAny {P = P} {xs = xs} = (any (λ x → decide (P x) .value) xs) ⟨ Any-reflects-any P xs ⟩ where
    @0 Any-reflects-any : {A : Type} (P : A → Type) ⦃ _ : ∀{x} → Dec (P x) ⦄ (xs : List A)
      → Reflects (Any P xs) (any (λ x → decide (P x) .value) xs)
    Any-reflects-any P (x ∷ xs) = mapReflects
      {Either (P x) (Any P xs)}
      {Any P (x ∷ xs)}
      (λ where
        (Left h) → anyHere ⦃ h ⦄
        (Right h) → anyThere ⦃ h ⦄)
      (λ where
        (anyHere ⦃ h ⦄) → Left h
        (anyThere ⦃ h ⦄) → Right h)
      (Either-reflects-|| (reflects-decide (P x)) (Any-reflects-any P xs))

  {-# COMPILE AGDA2HS decAny inline #-}

  decNonEmpty : {a : Type} {xs : List a} → Dec (NonEmpty xs)
  decNonEmpty {xs = xs} = (not (null xs)) ⟨ NonEmpty-reflects-not-null xs ⟩ where
    NonEmpty-reflects-not-null : (xs : List a) → Reflects (NonEmpty xs) (not (null xs))
    NonEmpty-reflects-not-null (x ∷ xs) = itsNonEmpty

  {-# COMPILE AGDA2HS decNonEmpty inline #-}

  decBot : Dec ⊥
  decBot = False ⟨ id ⟩

  {-# COMPILE AGDA2HS decBot inline #-}

  decTop : Dec ⊤
  decTop = True ⟨ tt ⟩

  {-# COMPILE AGDA2HS decTop inline #-}
