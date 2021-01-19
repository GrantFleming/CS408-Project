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
    l : Lib
    d : Dir

-- substitution on terms
_⇒_ : Scope → Scope → Set
γ ⇒ δ = γ ⇒[ Term lib compu ] δ

_⟨σ_ : Thinnable (γ ⇒_)
σ ⟨σ θ = ⟨sub _⟨term_ σ θ

_^` : (γ ⇒ δ) → γ ⇒ (suc δ)
σ ^` = σ ⟨σ ↑

id : γ ⇒ γ
id {zero} = ε
id {suc γ} = ^sub {T = Term lib compu} _⟨term_ (id {γ}) -, ess (var (fromNum γ))

_++sub_ : (δ ⇒ γ) → (δ' ⇒ γ) → (δ + δ') ⇒ γ
ε        ++sub σ' = σ'
(σ -, x) ++sub σ' = (σ ++sub σ') -, x

-- action of a substitution
_/term_ : Term l d γ → γ ⇒ δ → Term lib d δ

_/term_ {ess} {const} (` x)       σ  = ess (` x)
_/term_ {ess} {const} (s ∙ t)     σ  = ess ((s /term σ) ∙ (t /term σ))
_/term_ {ess} {const} (bind t)    σ  = ess (bind (t /term (σ ^` -, ess (var ze))))

_/term_ {ess} {compu} (var v)     σ  with ⟦ v ⟧var ! σ
...                                 | ε -, x        = x
_/term_ {ess} {compu} (elim e s)  σ  = ess (elim (e /term σ) (s /term σ))

_/term_ {lib} {const} (ess x)     σ  = x /term σ
_/term_ {lib} {const} (thunk x)   σ  = ↠ (x /term σ)
_/term_ {lib} {compu} (ess x)     σ  = x /term σ
_/term_ {lib} {compu} (t ∷ T)     σ  = (t /term σ) ∷ (T /term σ)
\end{code}

