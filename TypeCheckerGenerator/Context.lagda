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
We define contexts to be substitutions of constructions. We ensure that the target
of the substitution is scoped identically to the things we will substitute,
keeping our contexts in a pre-thinned state.This allows us to use terms
directly from it without having to fix up the scope first.
\begin{code}
Context : Scope → Set
Context γ = γ ⇒[ Const ] γ
\end{code}
\hide{
\begin{code}

_⟨Γ_  : Thinnable (δ ⇒[ Const ]_)
_^Γ   : Weakenable (δ ⇒[ Const ]_)

_‼V_ : Var γ → (Context γ) → Const γ
v ‼V Γ = lookup (Const) Γ v

Γ ⟨Γ θ = ⟨sub _⟨term_ Γ θ
_^Γ = weaken _⟨Γ_
\end{code}
}
We provide a special function to extend contexts which appends a new
element to the context (making it no longer a context as $suc γ \neq γ$ in
$(suc γ) ⇒[ \mbox{Const} ]\; γ$) before weakening the whole substitution
yielding the context $(suc γ)\; \mbox{⇒[Const]} \;(suc γ)$. The extra effort
exerted here keeps our contexts in the previously explained pre-thinned state.

\begin{code}
_,_ : Context γ → Const γ → Context (suc γ)
Γ , t = (Γ -, t) ^Γ
\end{code}
If we only ever use $ε$ (for creating an empty backwards vector) and $\_ , \_$
to construct our contexts, we can be assured that they will always be valid and
pre-thinned. No such assurances can be made if the raw vector appending data
constructor $\_ -,\_$ is used.
\hide{
\begin{code}
_/Γ_ : δ ⇒[ Const ] γ → γ ⇒ γ' → δ ⇒[ Const ] γ'
Γ /Γ σ = map (_/term σ) Γ
\end{code}
}
