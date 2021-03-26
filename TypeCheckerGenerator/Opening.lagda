\section{Openings}
\label{sec:Opening}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Opening where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage using (Scope; Scoped)
open import Data.Nat using (_+_)
\end{code}
}

A useful operation later will be to open up scoped entities. We take this
to mean lifting an entity to include some scope $γ$ without capturing
anything scoped in $γ$. When opening some entity scoped in $δ$ by $γ$, the
result is an entity scoped in $γ + δ$ Any reference to something in
scope refers to the same thing it did before it was opened. If some entity
scoped in $δ$ has an action of a thinning defined for it, opening it by $γ$
may be defined as the action of the thinning $γ ◃ δ$.
\begin{code}
Openable : (T : Scoped) → Set
Openable T = ∀ {δ} → (γ : Scope) → T δ → T (γ + δ)
\end{code}
As with previous concepts, we adopt a naming convention when constructing
openings where we begin identifiers with "⊗".
