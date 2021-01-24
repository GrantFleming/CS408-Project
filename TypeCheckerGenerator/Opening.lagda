\section{Opening}
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
loosly to mean lifting an entity to include some scope $γ$ without capturing
anything scoped in $γ$ or otherwise acting on this new extension of the
scope. For example a variable scoped in $δ$ might be opened so that it is
now valid in scope $γ + δ$ where it will remain a reference to the same
information as before, opening it will not change its function

For thinnings, this is accomplished by prepending the identity thinning
length $γ$ to the original thinning so that for some $δ ⊑ δ'$ the resulting
thinning is of type $(γ + δ) ⊑ (γ + δ')$.

In general, for scoped entities we provide the following definition to
construct types that describe openings.

\begin{code}
Openable : (T : Scoped) → Set
Openable T = ∀ {δ} → (γ : Scope) → T δ → T (γ + δ)
\end{code}

As with previous concepts, we adopt a naming convension when constructing
openings where we use ⊗ often suffexed to identify the kind of thing we
are opening.

If some entity scoped in $δ$ has an action of a thinning defined for it,
opening it by $γ$ may be defined as thinning it by $γ ▹ δ$. \hl{check this}

