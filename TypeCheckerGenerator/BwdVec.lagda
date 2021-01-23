\section{BwdVec}

\hide
\begin{code}
module BwdVec where
\end{code}
}

\hide
\begin{code}
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
\end{code}
}

\hide
\begin{code}
private
  variable
    X : Set
    Y : Set
    n : ℕ
    m : ℕ
\end{code}
}

\begin{code}
data BwdVec (X : Set) : ℕ → Set where
  ε    : BwdVec X 0
  _-,_ : {n : ℕ} → BwdVec X n → X → BwdVec X (suc n)

infixl 20 _-,_

map : (X → Y) → BwdVec X n → BwdVec Y n
map f  ε       = ε
map f (v -, x) = map f v -, f x

_++_ : BwdVec X n → BwdVec X m → BwdVec X (n + m)
_++_ {n = n} v ε
  rewrite +-identityʳ n = v
_++_ {n = n} {m = suc m} v (v' -, x)
  rewrite +-suc n m = (v ++ v') -, x
\end{code}

