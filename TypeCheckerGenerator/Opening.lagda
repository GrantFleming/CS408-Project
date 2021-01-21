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

\begin{code}
-- scoped things can are openable
Openable : (T : Scoped) → Set
Openable T = ∀ {δ} → (γ : Scope) → T δ → T (γ + δ)
\end{code}
