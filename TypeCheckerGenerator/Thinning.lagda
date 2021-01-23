\section{Thinnings}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Thinning where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat.Properties using (+-suc; +-identityʳ)
{-# REWRITE +-suc +-identityʳ #-} -- to avoid the tedium

open import CoreLanguage
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Bool using (Bool)
open import Data.Empty renaming (⊥ to bot)
open import Data.Unit renaming (⊤ to top)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong)
open import BwdVec
open import Substitution
\end{code}

\begin{code}
private
  variable
    γ : Scope
    γ' : Scope
    δ : Scope
    δ' : Scope
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

-- appending a thinning
_++_ : δ ⊑ γ → δ' ⊑ γ' → (δ + δ') ⊑ (γ + γ')
_++_ {δ} {γ} θ ε
  rewrite +-identityʳ δ | +-identityʳ γ
  = θ
_++_ {γ = γ} {γ' = suc γ'} θ (ϕ O)
  rewrite +-suc γ γ'
  = (θ ++ ϕ) O
_++_ {δ} {γ} {suc δ'} {suc γ'} θ (ϕ I)
  rewrite +-suc δ δ'
        | +-suc γ γ'
        =  (θ ++ ϕ) I

++-identityʳ : (θ : δ ⊑ γ) → ε ++ θ ≡ θ
++-identityʳ  ε    = refl
++-identityʳ (θ O) = cong _O (++-identityʳ θ)
++-identityʳ (θ I) = cong _I (++-identityʳ θ)

-- Thinnability
Thinnable : Scoped → Set
Thinnable X = ∀ {δ} {γ} → X δ → (δ ⊑ γ) → X γ

-- Selectability (the opposite of thinning)
Selectable : Scoped → Set
Selectable X = ∀ {δ} {γ} → (δ ⊑ γ) → X γ → X δ

-- thinning composition
-- action of a thinning on a thining
_∘_ : Thinnable (γ₁ ⊑_)
ε     ∘  ε    = ε
θ     ∘ (ϕ O) = (θ ∘ ϕ) O
(θ O) ∘ (ϕ I) = (θ ∘ ϕ) O
(θ I) ∘ (ϕ I) = (θ ∘ ϕ) I

-- variables are thinnable
_⟨var_ : Thinnable Var
v    ⟨var (θ O) = su (v ⟨var θ)
ze   ⟨var (θ I) = ze
su v ⟨var (θ I) = su (v ⟨var θ)

-- we can thin opened variables
_⟨var⊗_ : Thinnable (λ δ → Var (γ + δ))
v ⟨var⊗  ε    = v
v ⟨var⊗ (θ O) = su (v ⟨var⊗ θ)
v ⟨var⊗ (θ I) = v ⟨var⊗ θ

-- variables are singleton thinnings
⟦_⟧var : Var γ → 1 ⊑ γ
⟦_⟧var {suc s} ze     = Ø I
⟦_⟧var {suc s} (su v) = ⟦ v ⟧var O

private
  variable
    d : Dir
    X : Set
    Y : Set
    n : ℕ

-- terms are thinnable
_⟨term_ : Thinnable (Term d)
_⟨term_ {const} (` x)      θ  = ` x
_⟨term_ {const} (s ∙ t)    θ  = (s ⟨term θ) ∙ (t ⟨term θ)
_⟨term_ {const} (bind t)   θ  = bind (t ⟨term (θ I))
_⟨term_ {const} (thunk x)  θ  = thunk (x ⟨term θ)
_⟨term_ {compu} (var x)    θ  = var (x ⟨var θ)
_⟨term_ {compu} (elim e s) θ  = elim (e ⟨term θ) (s ⟨term θ)
_⟨term_ {compu} (t ∷ T)    θ  = (t ⟨term θ) ∷ (T ⟨term θ)

-- we can thin an opened term
_⟨term⊗_ : Thinnable (λ δ → Term d (γ + δ))
_⟨term⊗_ {const} (` x)       θ = ` x
_⟨term⊗_ {const} (s ∙ t)     θ = (s ⟨term⊗ θ) ∙ (t ⟨term⊗ θ)
_⟨term⊗_ {const} (bind x)    θ = bind (x ⟨term⊗ θ)
_⟨term⊗_ {const} (thunk x)   θ = thunk (x ⟨term⊗ θ)
_⟨term⊗_ {compu} (var x)     θ = var (x ⟨var⊗ θ)
_⟨term⊗_ {compu} (elim e s)  θ = elim (e ⟨term⊗ θ) (s ⟨term⊗ θ)
_⟨term⊗_ {compu} (t ∷ T)     θ = (t ⟨term⊗ θ) ∷ (T ⟨term⊗ θ)

-- We can select from BwdVec using a thinning
_!_ : Selectable (BwdVec X)
ε     ! ε         = ε
(θ O) ! (xs -, x) = θ ! xs
(θ I) ! (xs -, x) = (θ ! xs)-, x

-- injections
_◃_ : (γ : Scope) → (δ : Scope) → γ ⊑ (γ + δ)
γ ◃ zero   = ι {γ}
γ ◃ suc δ  = (γ ◃ δ) O

_▹_ : (γ : Scope) → (δ : Scope) → δ ⊑ (γ + δ)
γ ▹ zero   = Ø
γ ▹ suc δ  rewrite +-suc γ δ = (γ ▹ δ) I

-- and substitutions are thinnable
-- if the thing it is substituting is thinnable
⟨sub : ∀ {T} → Thinnable T → Thinnable (δ ⇒[ T ]_)
⟨sub ⟨T ε θ        = ε
⟨sub ⟨T (σ -, x) θ = ⟨sub ⟨T σ θ -, ⟨T x θ

-- weakening
Weakening : Set
Weakening = ∀ {γ} → γ ⊑ (suc γ)

↑ : Weakening
↑ {γ} = ι O

-- a Weakening has an action on a Weakenable thing
Weakenable : Scoped → Set
Weakenable T = ∀ {γ} → T γ → T (suc γ)

-- we can weaken anything thinnable
weaken : {T : Scoped} → Thinnable T → Weakenable T
weaken {T} ⟨ t = ⟨ t ↑

-- so for a start we can weaken thinnings themselves
_^ : Weakenable (γ ⊑_)
_^ = weaken _∘_

-- variables are weakenable
_^var : Weakenable Var
_^var = weaken _⟨var_

-- terms are weakenable
_^term : Weakenable (Term d)
_^term {d} t = weaken {Term d} _⟨term_ t

-- substitutions are Weakenable if the thing
-- they substitute is Thinnable
^sub : ∀ {T} → Thinnable T → Weakenable (δ ⇒[ T ]_)
^sub ⟨T ε                  = ε
^sub ⟨T {γ} (_-,_ {n} σ x) = (^sub ⟨T {γ} σ) -, weaken ⟨T x
\end{code}
}
