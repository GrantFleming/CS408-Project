\section{Thinnings}
\label{section-thinnings}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Thinning where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat.Properties using (+-suc; +-identityʳ)
{-# REWRITE +-suc +-identityʳ #-} -- to avoid the tedium

open import CoreLanguage
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Bool using (Bool)
open import Data.Empty renaming (⊥ to bot)
open import Data.Unit using () renaming (⊤ to top)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong)
open import BwdVec hiding (_++_)
open import Substitution
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)
\end{code}
}

\hide{
\begin{code}
private
  variable
    γ : Scope
    γ' : Scope
    δ : Scope
    δ' : Scope
    γ₁ : Scope
    γ₂ : Scope
    γ₃ : Scope
    d : Dir
    T : Scoped
    X : Set
    Y : Set
    n : ℕ
\end{code}
}

A key concept that will be used throughout this implementation is that
of a thinning. Thinnings describe embeddings between scopes and are
denoted $δ ⊑ γ$ where they are embed some scope $δ$ into another
scope $γ$ and as such it must be that $δ \leq γ$.

Some thinning $δ ⊑ γ$ can be represented a a bit-vector $γ$ digits long where
each digit might be $0$ indicating that the variable is new in $γ$ or $I$
indicating that it previously existed in $δ$. A thinning may also be interpreted
as a selection from some scope $γ$, and we may use singleton thinnings in
order to represent variables in this way. Our implementation maintains the
$δ \leq γ$ invariant by construction and is shown here.

\begin{code}
data _⊑_ : Scope → Scope → Set where
  ε   : 0 ⊑ 0
  _O  : γ ⊑ δ → γ ⊑ suc δ
  _I  : γ ⊑ δ → suc γ ⊑ suc δ
\end{code}

We define some elements for later use: the identity thinning, the empty
thinning and what it means to append two thinnings as well as injections
to a concatenation in both directions. Their type signatures are as follows.

\begin{code}
ι     : γ ⊑ γ
Ø     : 0 ⊑ γ
_++_  : δ ⊑ γ → δ' ⊑ γ' → (δ + δ') ⊑ (γ + γ')
_◃_   : (γ δ : Scope) → γ ⊑ (γ + δ)
_▹_   : (γ δ : Scope) → δ ⊑ (γ + δ)
\end{code}

\hide{
\begin{code}
ι {zero}  = ε
ι {suc γ} = ι I

Ø {zero}  = ε
Ø {suc γ} = Ø O

_++_ {δ} {γ} θ ε
  rewrite +-identityʳ δ | +-identityʳ γ
  = θ
_++_ {γ = γ} {γ' = suc γ'} θ (ϕ O)
  rewrite +-suc γ γ'
  = (θ ++ ϕ) O
_++_ {δ} {γ} {suc δ'} {suc γ'} θ (ϕ I)
  rewrite +-suc δ δ'
        | +-suc γ γ'
        =  (θ ++ ϕ) I

γ ◃ zero   = ι {γ}
γ ◃ suc δ  = (γ ◃ δ) O

γ ▹ zero   = Ø
γ ▹ suc δ  rewrite +-suc γ δ = (γ ▹ δ) I
\end{code}
}
\hide{
\begin{code}
_≟_ : DecidableEquality (δ ⊑ γ)
ε     ≟  ε    = yes refl
(x O) ≟ (y O) with x ≟ y
... | yes refl = yes refl
... | no p     = no (λ { refl → p refl})
(x O) ≟ (y I) = no (λ {()})
(x I) ≟ (y O) = no (λ {()})
(x I) ≟ (y I) with x ≟ y
... | yes refl = yes refl
... | no p     = no (λ { refl → p refl})
\end{code}
}
\hide{
\begin{code}
++-identityʳ : (θ : δ ⊑ γ) → ε ++ θ ≡ θ
++-identityʳ  ε    = refl
++-identityʳ (θ O) = cong _O (++-identityʳ θ)
++-identityʳ (θ I) = cong _I (++-identityʳ θ)
\end{code}
}
\hide{
\begin{code}
-- Variables can be represented as singleton thinnings.
⟦_⟧var : Var γ → 1 ⊑ γ
⟦_⟧var {suc s} ze     = Ø I
⟦_⟧var {suc s} (su v) = ⟦ v ⟧var O
\end{code}
}

There are various scoped entities on which it makes sense for thinnings
to act by lifting the entity into a wider scope. To capture this commonly
used behaviour we introduce the concept of Thinnable and also provide its
counterpart Selectable for the opposite action of using some thinning to
somehow narrow the scope.

\begin{code}
Thinnable : Scoped → Set
Thinnable X = ∀ {δ} {γ} → X δ → (δ ⊑ γ) → X γ

Selectable : Scoped → Set
Selectable X = ∀ {δ} {γ} → (δ ⊑ γ) → X γ → X δ
\end{code}

There are many scoped entities that we will wish a thinning to act on,
and so we adopt the convention that all functions detailing an action
of thinnings begin with "⟨" except the action of a thinning on another
thinning which equates to composition and so we use the more traditional
$∘$ notation.

\begin{code}
_∘_       : Thinnable (δ ⊑_)
_⟨var_    : Thinnable Var
_⟨term_   : Thinnable (Term d)
\end{code}

\hide{
\begin{code}
_⟨var⊗_   : Thinnable (λ δ → Var (γ + δ))
_⟨term⊗_  : Thinnable (λ δ → Term d (γ + δ))
⟨sub      : Thinnable T → Thinnable (δ ⇒[ T ]_)

ε     ∘  ε    = ε
θ     ∘ (ϕ O) = (θ ∘ ϕ) O
(θ O) ∘ (ϕ I) = (θ ∘ ϕ) O
(θ I) ∘ (ϕ I) = (θ ∘ ϕ) I

v    ⟨var (θ O) = su (v ⟨var θ)
ze   ⟨var (θ I) = ze
su v ⟨var (θ I) = su (v ⟨var θ)

v ⟨var⊗  ε    = v
v ⟨var⊗ (θ O) = su (v ⟨var⊗ θ)
v ⟨var⊗ (θ I) = v ⟨var⊗ θ

_⟨term_ {const} (` x)      θ  = ` x
_⟨term_ {const} (s ∙ t)    θ  = (s ⟨term θ) ∙ (t ⟨term θ)
_⟨term_ {const} (bind t)   θ  = bind (t ⟨term (θ I))
_⟨term_ {const} (thunk x)  θ  = thunk (x ⟨term θ)
_⟨term_ {compu} (var x)    θ  = var (x ⟨var θ)
_⟨term_ {compu} (elim e s) θ  = elim (e ⟨term θ) (s ⟨term θ)
_⟨term_ {compu} (t ∷ T)    θ  = (t ⟨term θ) ∷ (T ⟨term θ)

_⟨term⊗_ {const} (` x)       θ = ` x
_⟨term⊗_ {const} (s ∙ t)     θ = (s ⟨term⊗ θ) ∙ (t ⟨term⊗ θ)
_⟨term⊗_ {const} (bind x)    θ = bind (x ⟨term⊗ θ)
_⟨term⊗_ {const} (thunk x)   θ = thunk (x ⟨term⊗ θ)
_⟨term⊗_ {compu} (var x)     θ = var (x ⟨var⊗ θ)
_⟨term⊗_ {compu} (elim e s)  θ = elim (e ⟨term⊗ θ) (s ⟨term⊗ θ)
_⟨term⊗_ {compu} (t ∷ T)     θ = (t ⟨term⊗ θ) ∷ (T ⟨term⊗ θ)

⟨sub ⟨T ε θ        = ε
⟨sub ⟨T (σ -, x) θ = ⟨sub ⟨T σ θ -, ⟨T x θ
\end{code}
}

While Selectable is used far less often, there are key areas where it makes
sense, for instance in using a thinning to select elements from a vector.

\begin{code}
_!_ : Selectable (BwdVec X)
\end{code}

\hide{
\begin{code}
ε     ! ε         = ε
(θ O) ! (xs -, x) = θ ! xs
(θ I) ! (xs -, x) = (θ ! xs)-, x
\end{code}
}

A weakening is a special case of a thinning where the scope is extended by
one at its most local position, for instance when passing under a binder.
This concept is captured here, as well as the relavent type that details
the action of a weakening.

\begin{code}
↑ : γ ⊑ (suc γ)
↑ = ι O

Weakenable : Scoped → Set
Weakenable T = ∀ {γ} → T γ → T (suc γ)

weaken : Thinnable T → Weakenable T
weaken ⟨ t = ⟨ t ↑
\end{code}

When providing Weakenables, we adopt the naming convention of beginning their
identifers with "\^̂".


\begin{code}
_^      : Weakenable (γ ⊑_)
_^var   : Weakenable Var
_^term  : Weakenable (Term d)
\end{code}

\hide{
\begin{code}
-- a substitution is weakenable if the think it substitutes is
^sub    : Thinnable T → Weakenable (δ ⇒[ T ]_)

-- so for a start we can weaken thinnings themselves
_^ = weaken _∘_

-- variables are weakenable
_^var = weaken _⟨var_

-- terms are weakenable

_^term {d} = weaken {Term d} _⟨term_

-- substitutions are Weakenable if the thing
-- they substitute is Thinnable
-- map!!!
^sub ⟨T = map (weaken ⟨T)
\end{code}
}
