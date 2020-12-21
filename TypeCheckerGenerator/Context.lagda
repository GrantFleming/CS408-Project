\section{A Notion of Context}

\hide{
\begin{code}
module Context where

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just)
open import Category.Monad.State using (StateT)
\end{code}
}

In our initial work, we begin with a simple notion of contexts, defining
them as backwards lists of types.

\begin{code}
data Bwd (A : Set) : Set where
  ε    : Bwd A
  _-,_ : Bwd A → A → Bwd A
\end{code}

\hide{
\begin{code}
private
  variable
    X : Set
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
