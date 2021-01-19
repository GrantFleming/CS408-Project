\section{Patterns}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Pattern where
\end{code}
}

\begin{code}
open import CoreLanguage renaming (↠ to ↠↠)
open import Thinning using (_⊑_; Ø; ι; _++_; ++-identityʳ; _⟨var_; _⟨term⊗_)
open import Data.Char using (Char) renaming (_≟_ to _is_)
open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Bool using (true; false)
open import Relation.Nullary using (does; _because_; proof; ofʸ)
open import Relation.Binary.PropositionalEquality using (refl;  _≡_; cong; cong₂)
open import Data.Nat using (suc; _+_)
\end{code}

\begin{code}
private
  variable
    δ : Scope
    γ : Scope
    γ' : Scope

-- a pattern
data Pattern (γ : Scope) : Set where
  `      : Char → Pattern γ
  _∙_    : Pattern γ → Pattern γ → Pattern γ
  bind   : Pattern (suc γ) → Pattern γ
  place  : {δ : Scope} → δ ⊑ γ → Pattern γ
  ⊥      : Pattern γ

private
  variable
    p : Pattern γ
    q : Pattern γ
    r : Pattern γ
    t : Pattern (suc γ)

infixr 20 _∙_

data _-Env {γ : Scope} : Pattern γ → Set where
  `      : {c : Char} → (` c) -Env
  _∙_    : q -Env → r -Env → (q ∙ r) -Env
  bind   : t -Env → (bind t) -Env
  thing  : {θ : δ ⊑ γ} → Term lib const δ → (place θ) -Env

-- We can 'open' patterns
_⊗_ : (γ : Scope) → (p : Pattern δ) → Pattern (γ + δ)
γ ⊗ ` x     = ` x
γ ⊗ (s ∙ t) = (γ ⊗ s) ∙ (γ ⊗ t)
_⊗_ {δ} γ (bind t)
  = bind (γ ⊗ t)
γ ⊗ place θ = place (ι ++ θ)
γ ⊗ ⊥       = ⊥

-- opening a pattern by 0 is just the pattern
⊗-identityʳ : 0 ⊗ p ≡ p
⊗-identityʳ {p = ` x}     = refl
⊗-identityʳ {p = p ∙ p₁}  = cong₂ _∙_ ⊗-identityʳ ⊗-identityʳ
⊗-identityʳ {p = bind p}  = cong bind ⊗-identityʳ 
⊗-identityʳ {p = place x} rewrite ++-identityʳ {θ = x} = refl
⊗-identityʳ {p = ⊥}       = refl

match : Term lib const (δ + γ) → (p : Pattern γ) → Maybe ((δ ⊗ p) -Env)
match (ess (` a)) (` c) with a is c
... | true because ofʸ refl = just `
... | _                     = nothing
match (ess (s ∙ t)) (p ∙ q)   = do
                                  x ← match s p
                                  y ← match t q
                                  just (x ∙ y)
match (ess (bind t)) (bind p) = do
                                  x ← match t p
                                  just (bind x)
match  {γ = γ} t   (place {δ'} θ) with γ ≟ δ'
... | true because ofʸ refl = just (thing t)
... | false because _       = nothing
match _ _                   = nothing

--schematic variables

data svar : Pattern γ → Scope → Set where
  ⋆    : {θ : δ ⊑ γ} → svar (place θ) δ -- ⋆ marks the spot
  _∙   : svar p δ → svar (p ∙ q) δ
  ∙_   : svar q δ → svar (p ∙ q) δ
  bind : svar q δ → svar (bind q) δ

-- we can remove places from a pattern identified with a schematic variable
_-_ : (p : Pattern γ) → svar p δ → Pattern γ
(p ∙ q) - (ξ ∙)  = (p - ξ) ∙ q
(p ∙ q) - (∙ ξ)  = p ∙ (q - ξ)
bind p  - bind ξ = bind (p - ξ)
place x - ⋆      = ` '⊤' 

-- we can also remove places from a pattern environment in a similar way
_-penv_ : p -Env → (ξ : svar p δ) → (p - ξ) -Env
(s ∙ t) -penv (ξ ∙) = (s -penv ξ) ∙ t
(s ∙ t) -penv (∙ ξ) = s ∙ (t -penv ξ)
bind e -penv bind ξ = bind (e -penv ξ)
thing x -penv ⋆     = `

-- we can 'open up' a svar
_⊗svar_ : svar p δ → (γ : Scope) → svar (γ ⊗ p) (γ + δ)
(⋆ {θ = θ}) ⊗svar γ = ⋆
(v ∙)       ⊗svar γ = (v ⊗svar γ) ∙
(∙ v)       ⊗svar γ = ∙ (v ⊗svar γ)
bind v      ⊗svar γ = bind (v ⊗svar γ)

-- and a var
_⊗var_ : Var δ → (γ : Scope) → Var (γ + δ)
(ze {s})   ⊗var γ = (fromNum γ) ⟨var ((ι {suc γ}) ++ (Ø {s}))
(su {s} v) ⊗var γ = su (v ⊗var γ)

-- we can 'open up' a term
_⊗term_ : ∀ {l} {d} → Term l d δ → (γ : Scope) → Term l d (γ + δ)
_⊗term_ {l = ess} {d = const} (` x)      γ = ` x
_⊗term_ {l = ess} {d = const} (s ∙ t)    γ = (s ⊗term γ) ∙ (t ⊗term γ)
_⊗term_ {l = ess} {d = const} (bind x)   γ = bind (x ⊗term γ)
_⊗term_ {l = ess} {d = compu} (var x)    γ = var (x ⊗var γ)
_⊗term_ {l = ess} {d = compu} (elim e s) γ = elim (e ⊗term γ) (s ⊗term γ)
_⊗term_ {l = lib} {d = const} (ess x)    γ = ess (x ⊗term γ)
_⊗term_ {l = lib} {d = const} (thunk x)  γ = thunk (x ⊗term γ)
_⊗term_ {l = lib} {d = compu} (ess x)    γ = ess (x ⊗term γ)
_⊗term_ {l = lib} {d = compu} (t ∷ T)    γ = (t ⊗term γ) ∷ (T ⊗term γ)

-- and we can open environments
_⊗env_ : p -Env → (γ : Scope) → (γ ⊗ p) -Env
`       ⊗env γ = `
(s ∙ t) ⊗env γ = (s ⊗env γ) ∙ (t ⊗env γ)
bind e  ⊗env γ = bind (e ⊗env γ)
thing x ⊗env γ = thing (x ⊗term γ)

-- crucually, we can now look up terms in an environment
_‼_ : ∀ {γ} {p : Pattern γ} → svar p δ → (γ' ⊗ p) -Env → Term lib const (γ' + δ)
⋆      ‼ thing x = x
(v ∙)  ‼ (p ∙ q) = v ‼ p
(∙ v)  ‼ (p ∙ q) = v ‼ q
bind v ‼ bind t  = v ‼ t

-- we can also get the term back from the pattern and the environment
termFrom : (p : Pattern γ) → (δ ⊗ p) -Env → Term lib const (δ + γ)
termFrom (` x) `              = ess (` x)
termFrom (p ∙ p₁) (e ∙ e₁)    = ess (termFrom p e ∙ termFrom p₁ e₁)
termFrom (bind p) (bind e)    = ess (bind (termFrom p e))
termFrom (place θ) (thing x₁) = x₁ ⟨term⊗ θ
termFrom ⊥ ()
\end{code}

