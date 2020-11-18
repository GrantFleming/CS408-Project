module Fold where

open import Level

private
  variable
    ℓ ℓ′ : Level
    A : Set ℓ
    B : Set

record Foldable (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  field
    foldr : (A → B → B) → B → F A → B
