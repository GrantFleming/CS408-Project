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

\hide{
\begin{code}
private
  variable
    δ : Scope
    γ : Scope
\end{code}
}

Substitutions are defined as backward vectors, vectors that grow by appending
elements to the right hand side as opposed to the left. A substitution is
defined in terms of two scopes, the scope of the target of substitution, and
the scope of the entities we will substitute into the target.

We are able to look up individual variables in a substitution, later we will
see that this is just a special case of using a thinning to select from a
subsitution but having dedicated syntax is often more convenient.

We also capture the idea of Substitutable entities and define composition
for substitution across all such definitions.

\begin{code}
_⇒[_]_ : Scope → Scoped → Scope → Set
γ ⇒[ X ] δ = BwdVec (X δ) γ

lookup : (T : Scoped) → δ ⇒[ T ] γ → Var δ → T γ

Substitutable : Scoped → Set
Substitutable T = ∀ {γ} {γ'} → T γ → γ ⇒[ T ] γ' → T γ'

[_]_∘σ_ : ∀ {T} → Substitutable T → Composable _⇒[ T ]_
\end{code}

\hide{
\begin{code}
lookup T (σ -, x) ze = x
lookup T (σ -, x) (su v) = lookup T σ v

[ / ]  ε       ∘σ σ' = ε
[ / ] (σ -, x) ∘σ σ' = ([ / ] σ ∘σ σ') -, / x σ'
\end{code}
}

