\section{A Notion of Context}

\hide{
\begin{code}
module Context where
open import Level
\end{code}
}

In our initial work, we begin with a simple notion of contexts, defining
them as backwards lists of types. We take care to produce a universe independent
implementation so that we might use it with our notion of Pattern.

\begin{code}
data Bwd {ℓ} (A : Set ℓ) : Set ℓ where
  ε    : Bwd A
  _-,_ : Bwd A → A → Bwd A
\end{code}

\hide{
\begin{code}
private
  variable
    ℓ : Level
    X : Set ℓ
    σ : X
    Γ : Bwd X
\end{code}
}

We use a de-bruijn index representation of variables.

\begin{code}
data Var (τ : X) : Bwd X → Set where
  ze : Var τ (Γ -, τ)
  su : Var τ Γ → Var τ (Γ -, σ)
\end{code}
