\section{Patterns}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Pattern where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Thinning using (_⊑_; Ø; ι; _++_; _⟨term⊗_; ++-identityʳ)
open import Data.String using (String; _==_)
open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Bool using (true; false)
open import Relation.Nullary using (does; _because_; proof; ofʸ)
open import Relation.Binary.PropositionalEquality using (refl;  _≡_; cong; cong₂)
open import Data.Nat using (zero; suc; _+_)
open import Opening using (Openable)
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

Key to implementing our generic type-checker, is the concept of a pattern. Our
rules are defined not in terms of concrete pieces of syntax, but in terms of
patterns of constructions, which we then match against concrete syntax.

Our concept of a pattern is structurally identical to that of a construction,
except that we exclude thunks, and introduce the notion of a \emph{place} which
may stand for any arbitrary construction scoped in some $δ$ so long as we show
how it might be thinned to $γ$.

The dual concept of a pattern is that of an environment. It is structurally
similar to a pattern except where a pattern may have a \emph{place}, an
environment answers this call with a \emph{thing} that can fit in the place.
As always, we must be careful to handle scope correctly in the case of $bind$
when constructing environments so that the underlying entity is defined in
the weakened scope.

Environments are indexed by a pattern so that we can ensure that it always
matches exactly the pattern intended (in that it has an identical structure
and a \emph{thing} for every \emph{place}). Consequently this allows us a
non-failable operation to generate a term from from pattern $p$ and its
associated $p\mbox{-Env}$

\begin{code}
data Pattern (γ : Scope) : Set where
  `      : String → Pattern γ
  _∙_    : Pattern γ → Pattern γ → Pattern γ
  bind   : Pattern (suc γ) → Pattern γ
  place  : {δ : Scope} → δ ⊑ γ → Pattern γ
\end{code}
\hide{
\begin{code}
infixr 20 _∙_
private
  variable
    p : Pattern γ
    q : Pattern γ
    r : Pattern γ
    t : Pattern (suc γ)
\end{code}
}
\begin{code}
data _-Env {γ : Scope} : Pattern γ → Set where
  `      : {s : String} → (` s) -Env
  _∙_    : q -Env → r -Env → (q ∙ r) -Env
  bind   : t -Env → (bind t) -Env
  thing  : {θ : δ ⊑ γ} → Term const δ → (place θ) -Env
\end{code}

We define the opening of a pattern by recursing structurally and opening
the thinnings of the places in the matter described in section \ref{sec:Opening}.

\begin{code}
_⊗_ : Openable Pattern
\end{code}

\hide{
\begin{code}
-- We can 'open' patterns
γ ⊗ ` x      = ` x
γ ⊗ (s ∙ t)  = (γ ⊗ s) ∙ (γ ⊗ t)
γ ⊗ (bind t) = bind (γ ⊗ t)
γ ⊗ place θ  = place (ι {γ} ++ θ)

-- opening a pattern by 0 is just the pattern
open import Thinning using (ε; _O; _I)
⊗-identityʳ : 0 ⊗ p ≡ p
⊗-identityʳ {p = ` x}     = refl
⊗-identityʳ {p = p ∙ p₁}  = cong₂ _∙_ ⊗-identityʳ ⊗-identityʳ
⊗-identityʳ {p = bind p}  = cong bind ⊗-identityʳ
⊗-identityʳ {p = place θ} rewrite ++-identityʳ θ = refl
\end{code}
}

We now have the required machinery to define pattern matching. We do not
define matching over some term and pattern scoped identially, but more 
generally over some term that might be operating in some wider scope. This
is crucial as a pattern is often defined in the empty scope so that we might
not refer to arbirary free variables when defining formal rules. When
type-checking, the terms we match against them may operate in a wider scope.

For this reason, our matching allows the matching of a term in some wider
scope, to a pattern in a potentially narrower scope and if it succeeds it
returns an environment for the \emph{opened} pattern.

\begin{code}
match : Term const (δ + γ) → (p : Pattern γ) → Maybe ((δ ⊗ p) -Env)
match  {γ = γ} t   (place {δ'} θ) with γ ≟ δ'
... | true because ofʸ refl = just (thing t)
... | false because _       = nothing
match (` a) (` c) with a == c
... | true   =  just `
... | false  =  nothing
match (s ∙ t) (p ∙ q)   = do
                            x ← match s p
                            y ← match t q
                            just (x ∙ y)
match (bind t) (bind p) = do
                            x ← match t p
                            just (bind x)

-- TO DO, THUNK MATCHING!! evaluate it to head normal form
-- or do we assume that hnf was attempted already?
match _ _                   = nothing
\end{code}

When contructing formal rules, it is critical that we are able to refer
to distinct places in a pattern. For this purpose we define a schematic
variable. This variable is able to trace a path through the pattern that
indexes it, terminating with a $⋆$ to mark the place we refer to. We
construct this concept with care to ensure it is well-scoped by construction.

Using a schematic variable, we are able to look up the term associated to
a place by an environment by merely proceeding structually down the path
described by the svar and extracting the term from the thing it points to.

\begin{code}
data svar : Pattern γ → Scope → Set where
  ⋆     : {θ : δ ⊑ γ} → svar (place θ) δ
  _∙    : svar p δ → svar (p ∙ q) δ
  ∙_    : svar q δ → svar (p ∙ q) δ
  bind  : svar q δ → svar (bind q) δ


_‼_ : svar p δ → (γ' ⊗ p) -Env → Term const (γ' + δ)
⋆       ‼ thing x  = x
(v ∙)   ‼ (p ∙ q)  = v ‼ p
(∙ v)   ‼ (p ∙ q)  = v ‼ q
bind v  ‼ bind t   = v ‼ t
\end{code}

We define a few less interesting but critical utility functions for later
use. We give a means to remove a place from a pattern, replacing it with
a trivial atom. Similarly we extend the same functionality to environments.

We also define some openings and a method for retrieving a term from a pattern
and some opening of its environment. We are unable to use our previously defined
Openable for schematic variables as the type is a little difference due to it
having a pattern index which also needs to be opened in the return type.

\begin{code}
_-_       : (p : Pattern γ) → svar p δ → Pattern γ
_-penv_   : p -Env → (ξ : svar p δ) → (p - ξ) -Env
_⊗svar_   : (γ : Scope) → svar p δ → svar (γ ⊗ p) (γ + δ)
_⊗var_    : Openable Var
termFrom  : (p : Pattern γ) → (δ ⊗ p) -Env → Term const (δ + γ)
\end{code}
\hide{
\begin{code}
(p ∙ q) - (ξ ∙)  = (p - ξ) ∙ q
(p ∙ q) - (∙ ξ)  = p ∙ (q - ξ)
bind p  - bind ξ = bind (p - ξ)
place x - ⋆      = ` "⊤"

(s ∙ t) -penv (ξ ∙) = (s -penv ξ) ∙ t
(s ∙ t) -penv (∙ ξ) = s ∙ (t -penv ξ)
bind e -penv bind ξ = bind (e -penv ξ)
thing x -penv ⋆     = `

γ ⊗svar ⋆      = ⋆
γ ⊗svar (v ∙)  = (γ ⊗svar v) ∙
γ ⊗svar (∙ v)  = ∙ (γ ⊗svar v)
γ ⊗svar bind v = bind (γ ⊗svar v)

γ ⊗var ze = ze
γ ⊗var su v = su (γ ⊗var v)

termFrom (` x) `              = ` x
termFrom (p ∙ p₁) (e ∙ e₁)    = termFrom p e ∙ termFrom p₁ e₁
termFrom (bind p) (bind e)    = bind (termFrom p e)
termFrom (place θ) (thing x₁) = x₁ ⟨term⊗ θ
\end{code}
}

