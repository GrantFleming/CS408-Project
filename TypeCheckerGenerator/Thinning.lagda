\section{Thinnings}

\begin{code}
module Thinning where

open import CoreLanguage
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool)
\end{code}

\begin{code}
private
  variable
    γ : Scope
    δ : Scope
    γ₁ : Scope
    γ₂ : Scope
    γ₃ : Scope

-- a thinning
data _⊑_ : Scope → Scope → Set where
  ε   : 0 ⊑ 0
  _O  : (θ : γ ⊑ δ) → γ ⊑ suc δ
  _I  : (θ : γ ⊑ δ) → suc γ ⊑ suc δ

-- identity thinning
ι : (γ : Scope) → γ ⊑ γ
ι zero = ε
ι (suc γ) = ι γ I

-- empty thinning
Ø : (γ : Scope) → 0 ⊑ γ
Ø zero = ε
Ø (suc γ) = Ø γ O

-- thinning composition
_∘_ : γ₁ ⊑ γ₂ → γ₂ ⊑ γ₃ → γ₁ ⊑ γ₃
ε     ∘  ε    = ε
θ     ∘ (ϕ O) = (θ ∘ ϕ) O
(θ O) ∘ (ϕ I) = (θ ∘ ϕ) O
(θ I) ∘ (ϕ I) = (θ ∘ ϕ) I

-- variables are thinnable
_⟨_ : Var γ → γ ⊑ δ → Var δ
ze   ⟨ (θ O)  = su (ze ⟨ θ)
ze   ⟨ (θ I)  = ze
su v ⟨ (θ O)  = su (su v ⟨ θ)
su v ⟨ (θ I)  = su (v ⟨ θ)

-- variables are singleton thinnings
⟦_⟧var : Var γ → 1 ⊑ γ
⟦_⟧var {suc s} ze     = Ø s I
⟦_⟧var {suc s} (su v) = ⟦ v ⟧var O

private
  variable
    l : Lib
    d : Dir
    X : Set
    Y : Set
    n : ℕ

-- terms are thinnable
_⟪_ : Term l d γ → γ ⊑ δ → Term l d δ
_⟪_ {ess} {const} (` x) θ       = ` x
_⟪_ {ess} {const} (s ∙ t) θ     = (s ⟪ θ) ∙ (t ⟪ θ)
_⟪_ {ess} {const} (bind t) θ    = bind (t ⟪ (θ I))
_⟪_ {ess} {compu} (var x) θ     = var (x ⟨ θ)
_⟪_ {ess} {compu} (elim e s) θ  = elim (e ⟪ θ) (s ⟪ θ)
_⟪_ {lib} {const} (ess x) θ     = ess (x ⟪ θ)
_⟪_ {lib} {const} (thunk x) θ   = thunk (x ⟪ θ)
_⟪_ {lib} {compu} (ess x) θ     = ess (x ⟪ θ)
_⟪_ {lib} {compu} (t ∷ T) θ     = (t ⟪ θ) ∷ (T ⟪ θ)

-- selection
data BwdVec (X : Set) : ℕ → Set where
  ε    : BwdVec X 0
  _-,_ : {n : ℕ} → BwdVec X n → X → BwdVec X (suc n)

infixl 20 _-,_

map : (X → Y) → BwdVec X n → BwdVec Y n
map f ε = ε
map f (xs -, x) = map f xs -, f x

_!_ : γ ⊑ δ  → BwdVec X δ → BwdVec X γ
ε     ! ε         = ε
(θ O) ! (xs -, x) = θ ! xs
(θ I) ! (xs -, x) = (θ ! xs)-, x

-- injections
_◃_ : (γ : Scope) → (δ : Scope) → γ ⊑ (δ + γ)
γ ◃ zero   = ι γ
γ ◃ suc δ  = (γ ◃ δ) O

_▹_ : (γ : Scope) → (δ : Scope) → δ ⊑ (δ + γ)
γ ▹ zero   = Ø γ
γ ▹ suc δ  = (γ ▹ δ) I

-- substitution
_⇒_ : Scope → Scope → Set
γ ⇒ δ = BwdVec (Term lib compu δ) γ

-- weakening
↑ : γ ⊑ (suc γ)
↑ {γ} = ι γ O

_^ : γ ⊑ δ → γ ⊑ (suc δ)
θ ^ = θ ∘ ↑

-- substitutions are thinnable
private
  variable
    δ` : Scope

_⟪⟨_ : (γ ⇒ δ) → (δ ⊑ δ`) → (γ ⇒ δ`)
ε        ⟪⟨ θ = ε
(σ -, x) ⟪⟨ θ = (σ ⟪⟨ θ) -, (x ⟪ θ)

_^` : (γ ⇒ δ) → γ ⇒ (suc δ)
σ ^` = σ ⟪⟨ ↑

-- action of a substitution
_/_ : Term l d γ → γ ⇒ δ → Term lib d δ

_/_ {ess} {const} (` x)       σ  = ess (` x)
_/_ {ess} {const} (s ∙ t)     σ  = ess ((s / σ) ∙ (t / σ))
_/_ {ess} {const} (bind t)    σ  = ess (bind (t / (σ ^` -, ess (var ze))))

_/_ {ess} {compu} (var v)     σ  with ⟦ v ⟧var ! σ
...                                 | ε -, x        = x
_/_ {ess} {compu} (elim e s)  σ  = ess (elim (e / σ) (s / σ))

_/_ {lib} {const} (ess x)     σ  = x / σ
_/_ {lib} {const} (thunk x)   σ  = ↠ (x / σ)
_/_ {lib} {compu} (ess x)     σ  = x / σ
_/_ {lib} {compu} (t ∷ T)     σ  = (t / σ) ∷ (T / σ)

-- identity substitution
ι⇒ : γ ⇒ γ
ι⇒ {zero}  = ε
ι⇒ {suc γ} = (ι⇒ {γ} ^`) -, ess (var ze)

-- substitution composition
_∘ₛ_ : (γ₁ ⇒ γ₂) → (γ₂ ⇒ γ₃) → (γ₁ ⇒ γ₃)
ε        ∘ₛ ρ = ε
(σ -, x) ∘ₛ ρ = (σ ∘ₛ ρ) -, (x / ρ)

\end{code}
