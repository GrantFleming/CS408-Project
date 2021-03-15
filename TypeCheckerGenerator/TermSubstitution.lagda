\section{Term Substitution}

\hide{
\begin{code}
module TermSubstitution where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Substitution
open import Thinning using (Thinnable; Weakenable; weaken; _⟨term_; ⟨sub)
open import BwdVec
open import Data.Nat using (zero; suc)
\end{code}
}

\hide{
\begin{code}
private
  variable
    δ : Scope
    δ' : Scope
    γ : Scope
    d : Dir
\end{code}
}

Following our generic notion of substitution, we now specialise our
our definiton to substitute computations. We supply the usual thinning
and weakening mechanics that we rely on as well as defining the identity
substitution.

\begin{code}
_⇒_ : Scope → Scope → Set
γ ⇒ δ = γ ⇒[ Compu ] δ

_⟨σ_  : Thinnable (γ ⇒_)
_^    : Weakenable (γ ⇒_)
id    : γ ⇒ γ
\end{code}

\hide{
\begin{code}

σ ⟨σ θ = ⟨sub _⟨term_ σ θ

_^ = weaken _⟨σ_

id {zero} = ε
id {suc γ} = (id {γ} ^) -, var ze
\end{code}
}

We also define the action of such a substitution on a term, where most cases
recurse on direct substructures as one might expect except for two cases of
interest. The first is that we must ensure we alter the substitution accordingly
as we pass under binders, introducing an identity substitution for the newly
bound variable but first fixing up the scope of the substitution we already have.
The second is where we find some variable and perform the actual substitution.
Here we do not use the Substitutable type defined previously as the target of
substitution may be either a construction or a computation, however the objects
we are substituting in are always computations. This type is reserved for use
later.

\begin{code}
_/term_ : Term d γ → γ ⇒ δ → Term d δ
-- ...
_/term_ {const} (bind t)    σ  = bind (t /term (σ ^ -, var ze))
_/term_ {compu} (var v)     σ  = lookup (Term compu) σ v
-- ...
\end{code}

\hide{
\begin{code}
_/term_ {const} (` x)       σ  = ` x
_/term_ {const} (s ∙ t)     σ  = (s /term σ) ∙ (t /term σ)
_/term_ {const} (thunk x)   σ  = ↠ (x /term σ)
_/term_ {compu} (elim e s)  σ  = elim (e /term σ) (s /term σ)
_/term_ {compu} (t ∷ T)     σ  = (t /term σ) ∷ (T /term σ)
\end{code}
}
