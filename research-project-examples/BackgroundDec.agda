module BackgroundDec where

open import Haskell.Prelude hiding (_≡_)
open import Haskell.Extra.Dec renaming (Dec to Dec')
open import Haskell.Extra.Refinement

data _≡_ {a : Type} (x : a) : a → Type where
  instance refl : x ≡ x

record Dec {a} (A : Type a) : Type a where
  constructor _⟨⟩
  field
    inhabited  : Bool
    @0 ⦃ witness ⦄ : if inhabited then A else (A → ⊥)

decNonEmpty : {xs : List a} → Dec (NonEmpty xs)
decNonEmpty {xs = []} = (False ⟨⟩) ⦃ λ { () } ⦄
decNonEmpty {xs = x ∷ xs} = True ⟨⟩

isomorphism : ∀{P} → (Dec P → Dec' P) × (Dec' P → Dec P )
isomorphism {P} .fst ((inhabited ⟨⟩) ⦃ p ⦄) = inhabited ⟨ of {P} p ⟩
isomorphism {P} .snd (inhabited ⟨ p ⟩)      = (inhabited ⟨⟩) ⦃ invert {P} p ⦄
