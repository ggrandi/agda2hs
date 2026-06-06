module Example3.Variant where

open import Haskell.Prelude

data Variant (a b : Type) : Type where
  Errors : List a → Variant a b
  Ok : b → Variant a b
