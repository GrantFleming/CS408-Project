\section{Representing Judgements and Rules}

\hide{
\begin{code}
module Rules where

open import Pattern using (Pattern)
open Pattern.Pattern
open import Data.List using (List; _∷_; [])
open import Context using (Context; Ty)
open import undefined
\end{code}
}

We now look at representing judgements and rules in our software.

We provide two judgements from which users can build the rules of their
type-system: one for type synthesis and another for type checking. These
are implemented as instances of our Pattern record type.

\begin{code}
-- type synthesis
-- Γ : a ∈ A
syn : Pattern
name  syn = 0
holes syn = Context ∷ undefined ∷ Ty ∷ []

-- type checking
-- Γ : A ∋ a
chk : Pattern
name chk = 1
holes chk = Context ∷ Ty ∷ undefined ∷ []
\end{code}

We not show how we may construct rules from these judgements.


But we need the ability to have metavariables between patterns.
\begin{code}
record Rule : Set₁ where
  field
    premise : List Pattern
    conclusion : Pattern
\end{code}
