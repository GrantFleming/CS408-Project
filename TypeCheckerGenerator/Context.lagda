\section{A Notion of Context}

\hide{
\begin{code}
module Context where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Thinning using (⟦_⟧var; _!_; Thinnable; ⟨sub; _⟨term_; Weakenable; weaken)
open import BwdVec
open import Data.Nat using (suc)
open import Substitution
open import TermSubstitution
\end{code}
}

\hide{
\begin{code}
private
  variable
    δ : Scope
    γ : Scope
    γ' : Scope
\end{code}
}

Building on our definitions of substitution and thinning we are now
able to describe our context.

A context is a substitution of constructions. We ensure that the target
of the substitution is scoped identically to the things we will substitute,
keeping our contexts in a pre-thinned state.This allows us to use terms
directly from it without having to fix up the scope first.

We define actions of thinnings and weakenings on substitutions of constructions
but are careful to note that by thinning or weakening a context, the result
is not necessarily a context as the scope of the targets and substituted terms
may no longer be equal.

\begin{code}
Context : Scope → Set
Context γ = γ ⇒[ Const ] γ

_⟨Γ_  : Thinnable (δ ⇒[ Const ]_)
_^Γ   : Weakenable (δ ⇒[ Const ]_)
\end{code}

\hide{
\begin{code}
_‼V_ : Var γ → (Context γ) → Const γ
v ‼V Γ = lookup (Const) Γ v

Γ ⟨Γ θ = ⟨sub _⟨term_ Γ θ
_^Γ = weaken _⟨Γ_
\end{code}
}

We provide a special function to extend contexts which appends a new
element to the context (making it no longer a context as $suc γ \neq γ$ in
$(suc γ) ⇒[ \mbox{Const} ] γ$) before weakening the whole substitution
yielding the context $(suc γ) \mbox{⇒[Const]} (suc γ)$. The extra effort
exerted here keeps our contexts in the previously explained pre-thinned state.

If we only ever use $ε$ and $\_ , \_$ to construct our contexts, we can be assured
that they will always be valid and pre-thinned. No such assurances can
be made if the raw vector appending data constructor $\_ -,\_$ is used.

\begin{code}
_,_ : Context γ → Const γ → Context (suc γ)
Γ , t = (Γ -, t) ^Γ
\end{code}

Finally, we define the application of a substitution of constructions
so that the substitution might be mapped across all elements in the
context conveniently, but again we are careful to note that applying
this action to a context may not yield a context as explained previously.
\begin{code}
_/Γ_ : δ ⇒[ Const ] γ → γ ⇒ γ' → δ ⇒[ Const ] γ'
\end{code}
\hide{
\begin{code}
Γ /Γ σ = map (_/term σ) Γ
\end{code}
}
