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
ι : {γ : Scope} → γ ⊑ γ
ι {zero}  = ε
ι {suc γ} = ι I

-- empty thinning
Ø : {γ : Scope} → 0 ⊑ γ
Ø {zero}  = ε
Ø {suc γ} = Ø O

-- thinning composition
_∘_ : γ₁ ⊑ γ₂ → γ₂ ⊑ γ₃ → γ₁ ⊑ γ₃
ε     ∘  ε    = ε
θ     ∘ (ϕ O) = (θ ∘ ϕ) O
(θ O) ∘ (ϕ I) = (θ ∘ ϕ) O
(θ I) ∘ (ϕ I) = (θ ∘ ϕ) I

-- variables are thinnable
_⟨var_ : Var γ → γ ⊑ δ → Var δ
ze   ⟨var (θ O)  = su (ze ⟨var θ)
ze   ⟨var (θ I)  = ze
su v ⟨var (θ O)  = su (su v ⟨var θ)
su v ⟨var (θ I)  = su (v ⟨var θ)

-- variables are singleton thinnings
⟦_⟧var : Var γ → 1 ⊑ γ
⟦_⟧var {suc s} ze     = Ø I
⟦_⟧var {suc s} (su v) = ⟦ v ⟧var O

private
  variable
    l : Lib
    d : Dir
    X : Set
    Y : Set
    n : ℕ

-- terms are thinnable
_⟨term_ : Term l d γ → γ ⊑ δ → Term l d δ
_⟨term_ {ess} {const} (` x) θ       = ` x
_⟨term_ {ess} {const} (s ∙ t) θ     = (s ⟨term θ) ∙ (t ⟨term θ)
_⟨term_ {ess} {const} (bind t) θ    = bind (t ⟨term (θ I))
_⟨term_ {ess} {compu} (var x) θ     = var (x ⟨var θ)
_⟨term_ {ess} {compu} (elim e s) θ  = elim (e ⟨term θ) (s ⟨term θ)
_⟨term_ {lib} {const} (ess x) θ     = ess (x ⟨term θ)
_⟨term_ {lib} {const} (thunk x) θ   = thunk (x ⟨term θ)
_⟨term_ {lib} {compu} (ess x) θ     = ess (x ⟨term θ)
_⟨term_ {lib} {compu} (t ∷ T) θ     = (t ⟨term θ) ∷ (T ⟨term θ)

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
γ ◃ zero   = ι
γ ◃ suc δ  = (γ ◃ δ) O

_▹_ : (γ : Scope) → (δ : Scope) → δ ⊑ (δ + γ)
γ ▹ zero   = Ø
γ ▹ suc δ  = (γ ▹ δ) I

-- substitution
_⇒[_]_ : Scope → (Scope → Set) → Scope → Set
γ ⇒[ X ] δ = BwdVec (X δ) γ

_⇒_ : Scope → Scope → Set
γ ⇒ δ = γ ⇒[ Term lib compu ] δ

-- weakening
↑ : γ ⊑ (suc γ)
↑ {γ} = ι O

_^ : γ ⊑ δ → γ ⊑ (suc δ)
θ ^ = θ ∘ ↑

-- substitutions are thinnable
private
  variable
    δ` : Scope

_⟨σ_ : (γ ⇒ δ) → (δ ⊑ δ`) → (γ ⇒ δ`)
ε        ⟨σ θ = ε
(σ -, x) ⟨σ θ = (σ ⟨σ θ) -, (x ⟨term θ)

_^` : (γ ⇒ δ) → γ ⇒ (suc δ)
σ ^` = σ ⟨σ ↑

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
ι⇒ {suc γ} = (ι⇒ ^`) -, ess (var ze)

-- substitution composition
_∘ₛ_ : (γ₁ ⇒ γ₂) → (γ₂ ⇒ γ₃) → (γ₁ ⇒ γ₃)
ε        ∘ₛ ρ = ε
(σ -, x) ∘ₛ ρ = (σ ∘ₛ ρ) -, (x / ρ)

\end{code}
