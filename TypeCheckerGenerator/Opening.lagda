\section{Opening}

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
open import Thinning using (Thinnable; Ø; ι; _++_; _▹_)
\end{code}
}

\begin{code}
-- scoped things can be openable
Openable : (T : Scoped) → Set
Openable T = ∀ {δ} → (γ : Scope) → T δ → T (γ + δ)

-- anything thinnable is automatically openable
openable : ∀ {T} → Thinnable T → Openable T
openable ⟨ {δ} = λ γ Tδ → ⟨ Tδ (γ ▹ δ)
\end{code}
