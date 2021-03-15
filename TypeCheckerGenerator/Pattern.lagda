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
open import Thinning using (_⊑_; Ø; ι; _++_; _⟨term⊗_; ++-identityʳ; Weakenable) renaming (_≟_ to _≟θ_)
open import Data.String using (String; _==_) renaming (_≟_ to _≟s_; _++_ to append)
open import Data.Nat.Properties renaming (_≟_ to _≟n_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong; cong₂; _≢_)
open import Relation.Binary.Definitions using (DecidableEquality; Decidable)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Opening using (Openable)
open import Function using (_∘_)
\end{code}
}

\hide{
\begin{code}
private
  variable
    δ : Scope
    δ' : Scope
    γ : Scope
    γ' : Scope
    d  : Dir
\end{code}
}

Key to implementing our generic type-checker, is the concept of a pattern. Our
rules are defined not in terms of concrete pieces of syntax, but in terms of
patterns of constructions, which we then match against concrete syntax.

Our concept of a pattern is structurally identical to that of a construction,
except that we exclude thunks, and introduce the notion of a \emph{place} which
may stand for any arbitrary construction scoped in some $δ$ so long as we show
how it might be thinned to the scope of the pattern.

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
  ⊥      : Pattern γ
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
  thing  : {θ : δ ⊑ γ} → Const δ → (place θ) -Env
\end{code}

We define the opening of a pattern by recursing structurally and opening
the thinnings of the places in the matter described in section \ref{sec:Opening}.
We also provide means to map a function on terms over an environment.

\begin{code}
_⊗_ : Openable Pattern
map : (∀ {δ} → Const δ → Const (δ' + δ)) → p -Env → (δ' ⊗ p) -Env
\end{code}
\hide{
\begin{code}
-- We can 'open' patterns
γ ⊗ ` x      = ` x
γ ⊗ (s ∙ t)  = (γ ⊗ s) ∙ (γ ⊗ t)
γ ⊗ (bind t) = bind (γ ⊗ t)
γ ⊗ place θ  = place (ι {γ} ++ θ)
_ ⊗ ⊥        = ⊥

map f `         = `
map f (s ∙ t)   = map f s ∙ map f t
map f (bind t)  = bind (map f t)
map f (thing x) = thing (f x)

-- opening a pattern by 0 is just the pattern
open import Thinning using (ε; _O; _I)
⊗-identityʳ : 0 ⊗ p ≡ p
⊗-identityʳ {p = ` x}     = refl
⊗-identityʳ {p = p ∙ p₁}  = cong₂ _∙_ ⊗-identityʳ ⊗-identityʳ
⊗-identityʳ {p = bind p}  = cong bind ⊗-identityʳ
⊗-identityʳ {p = place θ} rewrite ++-identityʳ θ = refl
⊗-identityʳ {p = ⊥}       = refl

{-# REWRITE ⊗-identityʳ #-}

-- and decide if patterns are equal
_≟_ : DecidableEquality (Pattern γ)
` x       ≟ ` y with x ≟s y
... | yes refl = yes refl
... | no p     = no (λ { refl → p refl})
(x ∙ x₁)  ≟ (y ∙ y₁) with x ≟ y | x₁ ≟ y₁
... | no p  | no  p' = no (λ { refl → p refl})
... | no p  | yes p' = no (λ { refl → p refl})
... | yes p | no  p' = no (λ { refl → p' refl})
... | yes p | yes p' = yes (cong₂ _∙_ p p')
bind x    ≟ bind y with x ≟ y
... | yes refl = yes refl
... | no  p = no (λ { refl → p refl})
place {δ = δ} x   ≟ place {δ = δ'} y with δ ≟n δ'
... | no p     = no λ { refl → p refl  }
... | yes refl with x ≟θ y
... | yes refl = yes refl
... | no p = no (λ { refl → p refl})
⊥ ≟ ⊥ = yes refl

` x ≟ (y ∙ y₁)       = no (λ {()})
` x ≟ bind y         = no (λ {()})
` x ≟ place x₁       = no (λ {()})
` x ≟ ⊥              = no (λ {()})
(x ∙ x₁) ≟ ` x₂      = no (λ {()})
(x ∙ x₁) ≟ bind y    = no (λ {()})
(x ∙ x₁) ≟ place x₂  = no (λ {()})
(x ∙ x₁) ≟ ⊥         = no (λ {()})
bind x ≟ ` x₁        = no (λ {()})
bind x ≟ (y ∙ y₁)    = no (λ {()})
bind x ≟ place x₁    = no (λ {()})
bind x ≟ ⊥           = no (λ {()})
place x ≟ ` x₁       = no (λ {()})
place x ≟ (y ∙ y₁)   = no (λ {()})
place x ≟ bind y     = no (λ {()})
place x ≟ ⊥          = no (λ {()})
⊥ ≟ ` x              = no (λ {()})
⊥ ≟ (x ∙ x₁)         = no (λ {()})
⊥ ≟ bind x           = no (λ {()})
⊥ ≟ place x          = no (λ {()})

_/≟_ : ∀ {γ} → Decidable {A = Pattern γ} _≢_
x /≟ y with x ≟ y
... | yes refl = no λ to⊥ → to⊥ refl
... | no neq = yes neq
\end{code}
}
We now have the required machinery to define pattern matching. We do not
define matching over some term and pattern scoped identially, but more 
generally over some term that might be operating in some wider scope. This
is crucial as a pattern is often defined in the empty scope so that we might
not refer to arbirary free variables when defining formal rules. When
type-checking, the terms we match against them may operate in a wider scope.
If the matching then succeeds, it returns an environment for the \emph{opened}
pattern. In practice, this is always taken with $γ = 0$ where we are matching
some pattern defined in the empty scope.

\begin{code}
match : Const (δ + γ) → (p : Pattern γ) → Maybe ((δ ⊗ p) -Env)
match  {γ = γ} t   (place {δ'} θ) with γ ≟n δ'
... | yes refl = just (thing t)
... | no     _ = nothing
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


_‼_ : svar p δ → (γ' ⊗ p) -Env → Const (γ' + δ)
⋆       ‼ thing x  = x
(v ∙)   ‼ (p ∙ q)  = v ‼ p
(∙ v)   ‼ (p ∙ q)  = v ‼ q
bind v  ‼ bind t   = v ‼ t
\end{code}

We define a few less interesting but critical utility functions for later
use. We give a means to remove a place from a pattern, replacing it with
a trivial atom. Similarly we extend the same functionality to environments.
We  also define the usual spattering of openings and various other machinery
we have already covered, using the naming conventions discussed so they are
to be recognizable. In addition we provde here the type of the function that
produces an actual term from some pattern together with some environment.

\begin{code}
_-_       : (p : Pattern γ) → svar p δ → Pattern γ
_-penv_   : p -Env → (ξ : svar p δ) → (p - ξ) -Env
termFrom  : (p : Pattern γ) → (δ ⊗ p) -Env → Const (δ + γ)
\end{code}
\hide{
\begin{code}
(p ∙ q) - (ξ ∙)  = (p - ξ) ∙ q
(p ∙ q) - (∙ ξ)  = p ∙ (q - ξ)
bind p  - bind ξ = bind (p - ξ)
place x - ⋆      = ` "⊤"

_-svar_ : svar p δ → (ξ : svar p γ) → Maybe (svar (p - ξ) δ)
⋆    -svar  ⋆        = nothing
(v ∙) -svar (ξ ∙)    = v -svar ξ >>= λ n → just (n ∙)
(∙ v) -svar (∙ ξ)    = v -svar ξ >>= λ n → just (∙ n)
bind v -svar bind ξ  = v -svar ξ >>= λ n → just (bind n)
(v ∙) -svar (∙ ξ)    = just (v ∙)
(∙ v) -svar (ξ ∙)    = just (∙ v)

←_ : svar (p ∙ q) δ → svar (p ∙ q ∙ r) δ
← (v ∙) = v ∙
← (∙ v) = ∙ (v ∙)

(s ∙ t) -penv (ξ ∙) = (s -penv ξ) ∙ t
(s ∙ t) -penv (∙ ξ) = s ∙ (t -penv ξ)
bind e -penv bind ξ = bind (e -penv ξ)
thing x -penv ⋆     = `

_⊗svar_   : (γ : Scope) → svar p δ → svar (γ ⊗ p) (γ + δ)
γ ⊗svar ⋆      = ⋆
γ ⊗svar (v ∙)  = (γ ⊗svar v) ∙
γ ⊗svar (∙ v)  = ∙ (γ ⊗svar v)
γ ⊗svar bind v = bind (γ ⊗svar v)

_⊗var_    : Openable Var
γ ⊗var ze = ze
γ ⊗var su v = su (γ ⊗var v)

_⊗term_   : Openable (Term d)
_⊗term_ {const} γ (` x) = ` x
_⊗term_ {const} γ (s ∙ t) = (γ ⊗term s) ∙ (γ ⊗term t)
_⊗term_ {const} γ (bind t) = bind (γ ⊗term t)
_⊗term_ {const} γ (thunk x) = thunk (γ ⊗term x)
_⊗term_ {compu} γ (var x) = var (γ ⊗var x)
_⊗term_ {compu} γ (elim t e) = elim (γ ⊗term t) (γ ⊗term e)
_⊗term_ {compu} γ (t ∷ T) = (γ ⊗term t) ∷ (γ ⊗term T)

_⊗penv_   : (γ : Scope) → p -Env → (γ ⊗ p) -Env
_⊗penv_ γ  = map (γ ⊗term_)

termFrom (` x) `              = ` x
termFrom (p ∙ p₁) (e ∙ e₁)    = termFrom p e ∙ termFrom p₁ e₁
termFrom (bind p) (bind e)    = bind (termFrom p e)
termFrom (place θ) (thing x₁) = x₁ ⟨term⊗ θ

_^pat : Weakenable Pattern
` x ^pat      = ` x
(s ∙ t) ^pat  = (s ^pat) ∙ (t ^pat)
bind t ^pat   = bind (t ^pat)
place θ ^pat  = place (θ O)
⊥ ^pat        = ⊥

_^svar : svar p γ → svar (p ^pat) γ
⋆ ^svar = ⋆
(v ∙) ^svar = (v ^svar) ∙
(∙ v) ^svar = ∙ (v ^svar)
bind v ^svar = bind (v ^svar)
\end{code}
}

In a minor spoiler of things to come, we introduce the concept of an
svar-builder. We will later find it useful to traverse a pattern and build a
potential svar on the way down so that when we get to a $place$ we have the svar
that refers to it.

The notion is that instead of encoding some path to a $place$ in the pattern,
we instead encode some path between the pattern $p$ and some subpattern $q$. 
$X$ encodes an empty path between a pattern and itself, then we
may extend it, say with "\_∙" or "∙\_" so that we now show the path between
a pair, and one of the elements of that pair. We can continue in a similar fashion,
building some path, and if we are lucky enough to have it end in a $place$, then
we know we might convert it to the appropriate svar. This is normally used by
selecting both $p$ and $q$ to be the pattern we are about to traverse, then 
using the combinators as we traverse it to strip constructors off q while
simultaniously encoding that stripped constructor in the path being constructed.

\hide{
\begin{code}
private
  variable
    b : Bool
    lf rt p' : Pattern δ'
    bn : Pattern (suc δ')
    θ : δ ⊑ γ'
\end{code}
}

\begin{code}
data svar-builder : Pattern γ → Pattern δ → Set where
  X     : svar-builder p p
  _∙    : svar-builder p p' → svar-builder (p ∙ q) p'
  ∙_    : svar-builder q p' → svar-builder (p ∙ q) p'
  bind  : svar-builder p p' → svar-builder (bind p) p'
\end{code}

The combinators are fairly trivial but there types are important in showing
how we creating some distance between patterns in which we are charting some
path, by structurally reducing the second pattern in the type, but encoding
that information in the svar-builder we are creating so we remember exactly
how it was deconstructed. We give the first combinator in full here as an example,
and the types of the other two.

\begin{code}
⇚ : svar-builder p (lf ∙ rt) → svar-builder p lf
⇚ X          =  X ∙
⇚ (v ∙)      =  (⇚ v) ∙
⇚ (∙ v)      =  ∙ (⇚ v)
⇚ (bind  v)  =  bind (⇚ v )

⇛ : svar-builder p (lf ∙ rt) → svar-builder p rt 
↳ : svar-builder p (bind bn) → svar-builder p bn
\end{code}
\hide{
\begin{code}
⇛ X          =  ∙ X
⇛ (v ∙)      =  (⇛ v) ∙
⇛ (∙ v)      =  ∙ (⇛ v)
⇛ (bind  v)  =  bind (⇛ v)

↳ X          =  bind X
↳ (v ∙)      =  (↳ v) ∙
↳ (∙ v)      =  ∙ (↳ v)
↳ (bind  v)  =  bind (↳ v)
\end{code}
}

Finally we are able to build and actual svar from a builder only if it shows
the path in some pattern $p$ to some place in that pattern.

\begin{code}
build : {θ : δ ⊑ γ'} → 
        svar-builder p (place θ) → 
        svar p δ
build X         = ⋆
build (v ∙)     = (build v) ∙
build (∙ v)     = ∙ (build v)
build (bind v)  = bind (build v)
\end{code}

\hide{
\begin{code}
bind-count-bl : svar-builder p q → ℕ
bind-count-bl X = 0
bind-count-bl (v ∙) = bind-count-bl v
bind-count-bl (∙ v) = bind-count-bl v
bind-count-bl (bind v) = suc (bind-count-bl v)

lem1 : ∀{s t : Pattern γ}{v : svar-builder p (s ∙ t)} → bind-count-bl (⇚ v) ≡ bind-count-bl v
lem1 {v = X} = refl
lem1 {v = v ∙} = lem1 {v = v}
lem1 {v = ∙ v} = lem1 {v = v}
lem1 {v = bind v} = cong suc (lem1 {v = v})

lem2 : ∀{s t : Pattern γ}{v : svar-builder p (s ∙ t)} → bind-count-bl (⇛ v) ≡ bind-count-bl v
lem2 {v = X} = refl
lem2 {v = v ∙} = lem2 {v = v}
lem2 {v = ∙ v} = lem2 {v = v}
lem2 {v = bind v} = cong suc (lem2 {v = v})

lem3 : ∀{t : Pattern (suc γ)}{v : svar-builder p (bind t)} → bind-count-bl (↳ v) ≡ suc (bind-count-bl v)
lem3 {v = X} = refl
lem3 {v = v ∙} = lem3 {v = v}
lem3 {v = ∙ v} = lem3 {v = v}
lem3 {v = bind v} = cong suc (lem3 {v = v})

{-# REWRITE lem1 lem2 lem3 #-}

print-pat : Pattern γ → String
print-pat (` x)      = x
print-pat (p ∙ p₁)   = append (print-pat p) (append " " (print-pat p₁))
print-pat (bind p)   = append "bind " (print-pat p)
print-pat (place x)  = "PLACE"
print-pat ⊥          = "⊥"
\end{code}
}

