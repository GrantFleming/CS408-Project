\section{Substitution}

\hide{
\begin{code}
module Substitution where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import BwdVec
open import Composition
open import Data.Nat using (zero; suc)
\end{code}
}

\begin{code}
private
  variable
    δ : Scope
    γ : Scope

-- substitution
_⇒[_]_ : Scope → Scoped → Scope → Set
γ ⇒[ X ] δ = BwdVec (X δ) γ

-- we can select from substitions using _!_

-- we can lookup things in substitutions
lookup : (T : Scoped) → δ ⇒[ T ] γ → Var δ → T γ
lookup T (σ -, x) ze = x
lookup T (σ -, x) (su v) = lookup T σ v

-- Substitutability
Substitutable : Scoped → Set
Substitutable T = ∀ {γ} {γ'} → T γ → γ ⇒[ T ] γ' → T γ'

-- substitution composability
[_]_∘σ_ : ∀ {T} → Substitutable T → Composable _⇒[ T ]_
[ / ]  ε       ∘σ σ' = ε
[ / ] (σ -, x) ∘σ σ' = ([ / ] σ ∘σ σ') -, / x σ'
\end{code}

