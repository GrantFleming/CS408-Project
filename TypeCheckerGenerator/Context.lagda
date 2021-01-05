\section{A Notion of Context}

\hide{
\begin{code}
module Context where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Thinning using (_⇒[_]_; _⇒_; BwdVec; ε; _⊑_; _-,_; ⟦_⟧var; _!_; Thinnable; ⟨sub; _⟨term_; _/term_; _^term; ↑)
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

-- and we can apply substitutions generally to _⇒[ Term lib const ]_
-- but we are not guaranteed that the result will be a Context
-- unless γ = γ'
_/Γ_ : δ ⇒[ Term lib const ] γ → γ ⇒ γ' → δ ⇒[ Term lib const ] γ'
ε /Γ σ = ε
(Γ -, x) /Γ σ = (Γ /Γ σ) -, (x /term σ)

-- determin if something is a type (TEMPORARY - SWITCH ME WITH ACTUAL IMPLEMENTATION DOWN THE ROAD)
data Type : Term lib const γ → Set where

-- validity of contexts
-- im not sure if this is the best way or if I should just introduce
-- a test 'isValid' or a judgement do do this etc
data ValidContext : Context γ → Set where
  ε : ValidContext ε
  -- still need to work in that we should ensure t is a type
  _-,[_ , _] : {Γ : Context δ} → ValidContext Γ → (t : Term lib const δ) → Type t → ValidContext ((Γ ⟨Γ ↑) -, (t ^term))

\end{code}

