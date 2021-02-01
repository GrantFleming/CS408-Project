\section{A Core Language}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module CoreLanguage where
\end{code}

\begin{code}
open import Data.Nat using (ℕ; suc; zero)
open import Data.Char using (Char)
open import Data.String
\end{code}

\hide{
\begin{code}
\end{code}
}
}

The general tactic for type-checking generic code, will be to
convert user code into an internal language of our design. Our
internal language will be agnostic with regards to possible external
syntax but will have the key features needed to represent arbitrary
syntax.

First we introduce the concept of scope and what it means to be
scoped. In our system, all variables are de-bruijn indexed and our
scope can be represented by a single natural number. We take 0 to
mean nothing in scope, 1 to mean a single thing in scope etc. A
scoped entity is one which is defined in terms of a scope.

\begin{code}
Scope  = ℕ
Scoped = Scope → Set
\end{code}

A variable is our first example of such a scoped entity which we
construct in order to maintain the invariant that a variable should
always refer to something in scope.

\hide{
\begin{code}
private
  variable
    γ : Scope
    δ : Scope
\end{code}
}

\begin{code}
data Var : Scoped where
  ze : Var (suc γ)
  su : Var γ → Var (suc γ)
\end{code}

\hide{
\begin{code}
toNum : Var γ → ℕ
toNum ze     = 0
toNum (su v) = suc (toNum v)

fromNum : (n : ℕ) → Var (suc n)
fromNum zero = ze
fromNum (suc n) = su (fromNum n)
\end{code}
}


Our internal syntax is split into two broad grammatical
classes: constructions and computations. Constructions will have
their type checked, while computations have their type synthesized.

\hide{
\begin{code}
data Const (γ : Scope) : Set
data Compu (γ : Scope) : Set
\end{code}
}

\begin{code}
data Const γ where
  `      : Char → Const γ
  _∙_    : Const γ → Const γ → Const γ
  bind   : Const (suc γ) → Const γ
  thunk  : Compu γ → Const γ

data Compu γ where
  var    : Var γ → Compu γ
  elim   : Compu γ → Const γ → Compu γ
  _∷_    : Const γ → Const γ → Compu γ

data Dir : Set where const compu : Dir

Term : Dir → Scoped
Term const γ  = Const γ
Term compu γ  = Compu γ
\end{code}

This syntax gives us the means to represent atoms of original syntax
with `, pairs of syntax elements, binding sites (thus increasing the scope
for a subterm), variables, type annotated terms and eliminations - the
sites of $β$-reductions. We are also able to embed computations into
constructions, as we can always check the type of a synthesizable term by
synthesizing its type and ascertaining if it matches a provided
type.

Note that blindly embedding synthesizable terms with 'thunk' is
not always the best course of action \hl{why?}, in the case of an
annotated term, we already have a suitable construction under the
annotation. For convenience we provide a function to perform
this embedding.

\begin{code}
↠ : Compu γ → Const γ
↠ (t ∷ T) = t
↠  x      = thunk x
\end{code}

\hide{
\begin{code}
infixr 20 _∙_ 
private
  variable
    d : Dir

-- TO DO, explain this
-- turn anything into a const
↠↠ : Term d γ → Const γ
↠↠ {const} t = t
↠↠ {compu} t = ↠ t

print : Term d γ → String
print {const} (` x)      = fromChar x
print {const} (s ∙ t)    = print s ++ print t
print {const} (bind x)   = "(" ++ print x ++ ")"
print {const} (thunk x)  = "(_" ++ print x ++ "_)"
print {compu} (var x)    = "VAR"
print {compu} (elim e s) = "(elim " ++ print e ++ " " ++ print s ++ ")"
print {compu} (t ∷ T)    = "( {" ++ print t ++ "} ∶ " ++ print T ++ ")"

printrawvar : Var γ → String
printrawvar ze     = "ze"
printrawvar (su v) = "su " ++ printrawvar v

printraw : Term d γ → String
printraw {const} (` x)       = "(` '" ++ fromChar x ++ "')"
printraw {const} (s ∙ t)     = "(" ++ printraw s ++ " ∙ "  ++ printraw t ++ ")"
printraw {const} (bind x)    = "(bind " ++ printraw x ++ ")"
printraw {const} (thunk x)   = "(thunk " ++ printraw x ++ ")"
printraw {compu} (var x)     = "(var " ++ printrawvar x ++ ")"
printraw {compu} (elim e s)  = "(elim " ++ printraw e ++ " " ++ printraw s ++ ")"
printraw {compu} (t ∷ T)     = "(" ++ printraw t ++ "∶" ++ printraw T ++ ")"
\end{code}
}
