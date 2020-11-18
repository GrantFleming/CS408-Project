module Lists where



data Fwd (A : Set) : Set where
  ε    : Fwd A
  _:>_ : A → Fwd A → Fwd A

_⊗_ : ∀ {A} → Fwd A → Fwd A → Fwd A
_⊗_ ε         l₂ = l₂
_⊗_ (x :> l₁) l₂ = x :> (l₁ ⊗ l₂)





data Bwd (A : Set) : Set where
  ε    : Bwd A
  _:<_ : Bwd A → A → Bwd A
  
