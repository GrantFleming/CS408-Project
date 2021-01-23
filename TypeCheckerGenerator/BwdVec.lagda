\section{BwdVec}

\hide
\begin{code}
module BwdVec where
\end{code}
}

\hide
\begin{code}
open import Data.Nat using (ℕ; suc)
\end{code}
}

\begin{code}
data BwdVec (X : Set) : ℕ → Set where
  ε    : BwdVec X 0
  _-,_ : {n : ℕ} → BwdVec X n → X → BwdVec X (suc n)

infixl 20 _-,_

map : ∀ {X} {Y} {n} → (X → Y) → BwdVec X n → BwdVec Y n
map f  ε       = ε
map f (v -, x) = map f v -, f x
\end{code}

