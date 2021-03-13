\hide{
\begin{code}
module Composition where
\end{code}
}
\hide{
\begin{code}
open import CoreLanguage
\end{code}
}
\begin{code}
Composable : (Scope → Scope → Set) → Set
Composable X = ∀ {γ} {γ'} {γ''} → (X γ γ') → (X γ' γ'') → (X γ γ'')
\end{code}
