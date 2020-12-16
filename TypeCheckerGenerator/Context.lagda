\section{A Notion of Context}

\hide{
\begin{code}
module Context (VarName : Set) (T : Set) where
\end{code}
}

We begin by outlining the internal representation of contexts that will be used
heavily thoughout. Although a simple list captures the required functionality of
an ordered collection, we choose a more careful representation so that life is
a little easier down the line.

In preparation for constraint solving and polymorphism in future, we design our
contexts to make this process easier. Taking inspiration from Gundry, McBride
and McKinna \cite{TypeInferenceInContext} we use our context to explicitly track
type variables, and allow the contexts to container a marker for delimiting
Hindley-Milner style generalization later. We construct this entire module
generalizing over a representation of variable names (VarName) and types (T).

We firstly outline a context entry, allowing it to be attached to no declaration
so that we might introduce fresh variables.

\begin{code}
data Decl : Set where
  ‼  : T → Decl
  ⁇  : Decl

data Entry : Set where
  _∷=_  :  VarName → Decl → Entry
  ∥     :  Entry
\end{code}

We then define our contexts as backward lists of these entries.

\begin{code}
data Bwd (A : Set) : Set where
  ε     : Bwd A
  _-,_  : Bwd A → A → Bwd A

Context = Bwd Entry
\end{code}

Now we reconcile this notion of contexts with that of type and scope safe
syntax outlined by G. Allais et al. \cite{DBLP:journals/corr/abs-2001-11001} by
definining our free variables in terms of a context, except we have a concept
of variable names and we must ensure these match.

\hide{
\begin{code}
private
  variable
    Γ  : Context
\end{code}
}

\begin{code}
data FVar (v : VarName) (t : T) : Context → Set where
  top    : FVar v t (Γ -, (v ∷= ‼ t))
  under  : ∀ {e} → FVar v t Γ → FVar v t (Γ -, e)
\end{code}


