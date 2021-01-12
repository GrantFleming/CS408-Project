\section{A Notion of Context}

\hide{
\begin{code}
module Context where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Thinning using (_⇒[_]_; _⇒_; BwdVec; ε; _⊑_; _-,_; ⟦_⟧var; _!_; Thinnable; ⟨sub; _⟨term_; _/term_; _^term; ↑; Weakenable; weaken)
open import Data.Nat using (ℕ; zero; suc)
\end{code}
}

\begin{code}
Context : Scope → Set
Context γ = γ ⇒[ Term lib const ] γ

private
  variable
    δ : Scope
    γ : Scope
    δ'' : Scope
    δ' : Scope
    γ' : Scope

-- since contexts are just substitutions we can use the selection
-- already defined for BwdVec _!_ and define variables lookup in
-- terms of this
_‼V_ : Var γ → (Context γ) → Term lib const γ
v ‼V Γ with ⟦ v ⟧var ! Γ
... | ε -, x = x

-- we can apply a thinning generally to _⇒[ Term lib const ]_
-- but we are not guaranteed that the result will be a context
_⟨Γ_ : Thinnable (δ ⇒[ Term lib const ]_)
Γ ⟨Γ θ = ⟨sub _⟨term_ Γ θ

-- and therefore _⇒[ Term lib const ]_  can be weakened
-- (thus contexts can be weakened but are no longer contexts)
_^Γ : Weakenable (δ ⇒[ Term lib const ]_)
_^Γ = weaken _⟨Γ_

-- Which means we can define context extension
_,_ : Context γ → Term lib const γ → Context (suc γ)
Γ , t = (Γ -, t) ^Γ

-- Now if we only ever use ε and _,_ context extension, we are
-- guaranteed that our contexts WILL BE VALID AND PRE-THINNED

-- and we can apply substitutions generally to _⇒[ Term lib const ]_
-- but we are not guaranteed that the result will be a Context
-- unless γ = γ'
_/Γ_ : δ ⇒[ Term lib const ] γ → γ ⇒ γ' → δ ⇒[ Term lib const ] γ'
ε /Γ σ = ε
(Γ -, x) /Γ σ = (Γ /Γ σ) -, (x /term σ)

-- since contexts are just substitutions, we can look up variables in
-- contexts using 'Thinning.lookup'
\end{code}

