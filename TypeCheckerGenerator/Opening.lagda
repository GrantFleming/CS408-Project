\section{Opening}

\hide{
\begin{code}
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
to mean lifting an entity scoped in $δ$ by some scope $γ$ so that no part
of the entity refers to anything in $γ$, this is accomplished by assuming
there the outer and inner scopes do not intersect and so the result will be
some entity scoped in $γ + δ$.

\begin{code}
Openable : (T : Scoped) → Set
Openable T = ∀ {δ} → (γ : Scope) → T δ → T (γ + δ)
\end{code}

As with previous concepts, we adopt a naming convension when constructing
openings where we use ⊗ often suffexed with the kind of thing we are opening.
