\section{Failable}

\hide{
\begin{code}
module Failable where
\end{code}
}

\hide{
\begin{code}
open import Data.String using (String)
\end{code}
}

\hide{
\begin{code}
private
  variable
    A : Set
    B : Set
infixl 1 _>>=_    
\end{code}
}

To ready ourselves for the act of type-checking we here define our monad for
failure handling. We either succeed with a value, or fail with a string that
hopefully describes the error in a user friendly way.

\begin{code}
data Failable (X : Set) : Set where
  succeed : X → Failable X
  fail    : String → Failable X

_>>=_ : Failable A → (A → Failable B) → Failable B
succeed x >>= k = k x
fail x    >>= k = fail x

return : A → Failable A
return a = succeed a
\end{code}
