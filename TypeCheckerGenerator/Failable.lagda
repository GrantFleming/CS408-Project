\section{Failable}

\hide{
\begin{code}
module Failable where
\end{code}

\begin{code}
open import Data.String using (String)
\end{code}

\begin{code}
-- We can either succeed with a value, or fail with an error message
data Failable (X : Set) : Set where
  succeed : X → Failable X
  fail    : String → Failable X

-- Failable is a monad
private
  variable
    A : Set
    B : Set

infixl 1 _>>=_
_>>=_ : Failable A → (A → Failable B) → Failable B
succeed x >>= k = k x
fail x    >>= k = fail x

return : A → Failable A
return a = succeed a
\end{code}
}
