module ExamplePostulated.Postulated where

open import Haskell.Prelude
open import Haskell.Law.Functor using (IsLawfulFunctor)

postulate
  iLawfulFunctorFun : IsLawfulFunctor (λ b → a → b)
