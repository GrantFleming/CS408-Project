\section{Patterns and Instantiations}

\hide{
\begin{code}
module Pattern where

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.List.Relation.Unary.All
open import Function using (id)
open import Data.Bool using (Bool)
\end{code}
}

We begin by capturing the notion of a pattern. Patterns are an important
notion when describing type systems. The grammars which describe the syntax
are defined in terms of patterns, and judgement rules do not make sense
without them. To facilitate this functionality, we put forward a type of
patterns, a type of instantiations of patterns and a way of determining if
an instantiation matches a given pattern.

An internal representation of patterns need not hold the exact represenation
of every character in the syntax. By way of an example, consider a typing
rule whose conclusion is $λx.b$. This rule is a patterns meaning to stand
for an arbitrary lambda abstraction. We need not concern ourselve with the
exact syntax, a pattern need only consist of some identifier and two holes:
the first hole to be filled by and identifier, the second by a term.

We thus present the following definition of patterns.

\begin{code}
record Pattern : Set₁ where
  constructor _~_
  field
    name  : ℕ
    holes : List Set
\end{code}

\hide{
\begin{code}
open Pattern
\end{code}
}

An instantiation of a pattern is a list of values (one for each Set
corresponding to a hole in the pattern)

\begin{code}
Instantiation : Set₁
Instantiation = Σ[ p ∈ Pattern ] All id (holes p)
\end{code}

This representation makes checking for a pattern match trivial, as we
just check that the ids match.

\begin{code}
matches : Instantiation → Pattern → Bool
matches ((n ~ _) , _) (n' ~ _) = n ≡ᵇ n'
\end{code}

A possible gotcha here is that instantiations only match one pattern.
