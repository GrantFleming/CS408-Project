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
    T : Scoped
\end{code}
}

Substitutions are defined as backward vectors, vectors that grow by appending
elements to the right hand side as opposed to the left. A substitution is
defined in terms of two scopes, the scope of the target of substitution, and
the scope of the entities we will substitute into the target.

\begin{code}
_⇒[_]_ : Scope → Scoped → Scope → Set
γ ⇒[ X ] δ = BwdVec (X δ) γ
\end{code}

We are able to look up individual variables in a substitution, in section
\ref{section-thinnings} we explained that this is just a special case of
using a thinning to select from a subsitution but having dedicated syntax
is often more convenient and improves readability.

\begin{code}
lookup : (T : Scoped) → δ ⇒[ T ] γ → Var δ → T γ
\end{code}

We also capture a key notion that there is a type that describes scoped
things on which we may perform substitutions.

\begin{code}
Substitutable : Scoped → Set
Substitutable T = ∀ {γ} {γ'} → T γ → γ ⇒[ T ] γ' → T γ'
\end{code}

Finally, we acknowledge that given two scope transformations, we can define
a type to represent composition, which leads us nicely to a definition for
composition of substitutions.

\input{../../TypeCheckerGenerator/latex/Composition.tex}
\begin{code}
[_]_∘σ_ : Substitutable T → Composable _⇒[ T ]_
[ / ]  ε       ∘σ σ' = ε
[ / ] (σ -, x) ∘σ σ' = ([ / ] σ ∘σ σ') -, / x σ'
\end{code}

Although we will not use the definitions of Substitutable and Composable for
term substitution as we will soon see, these concepts will be useful in later
defintitions.

Here we have paid attention to the types in particular to aid readability of
later definitions. This can be seen in our final definition here which states
that given that some $T$ is substitutable, then we are able to compose the
subsitutions.

\hide{
\begin{code}
lookup T (σ -, x) ze = x
lookup T (σ -, x) (su v) = lookup T σ v
\end{code}
}

\usebox{\composable}

