\section{Term Substitution}

\hide
\begin{code}
module TermSubstitution where
\end{code}
}

\hide
\begin{code}
open import CoreLanguage
open import Substitution
open import Thinning using (Thinnable; ^sub; _⟨term_; ⟨sub; ↑; ⟦_⟧var; _!_)
open import BwdVec
open import Data.Nat using (zero; suc; _+_)
\end{code}
}

\begin{code}
private
  variable
    δ : Scope
    δ' : Scope
    γ : Scope
    d : Dir

-- substitution on terms
_⇒_ : Scope → Scope → Set
γ ⇒ δ = γ ⇒[ Term compu ] δ

_⟨σ_ : Thinnable (γ ⇒_)
σ ⟨σ θ = ⟨sub _⟨term_ σ θ

_^` : (γ ⇒ δ) → γ ⇒ (suc δ)
σ ^` = σ ⟨σ ↑

id : γ ⇒ γ
id {zero} = ε
id {suc γ} = ^sub {T = Term compu} _⟨term_ (id {γ}) -, var (fromNum γ)

_++sub_ : (δ ⇒ γ) → (δ' ⇒ γ) → (δ + δ') ⇒ γ
ε        ++sub σ' = σ'
(σ -, x) ++sub σ' = (σ ++sub σ') -, x

-- action of a substitution
_/term_ : Term d γ → γ ⇒ δ → Term d δ

_/term_ {const} (` x)       σ  = ` x
_/term_ {const} (s ∙ t)     σ  = (s /term σ) ∙ (t /term σ)
_/term_ {const} (bind t)    σ  = bind (t /term (σ ^` -, var ze))
_/term_ {const} (thunk x)   σ  = ↠ (x /term σ)

_/term_ {compu} (var v)     σ  with ⟦ v ⟧var ! σ
...                           | ε -, x        = x
_/term_ {compu} (elim e s)  σ  = elim (e /term σ) (s /term σ)
_/term_ {compu} (t ∷ T)     σ  = (t /term σ) ∷ (T /term σ)
\end{code}

