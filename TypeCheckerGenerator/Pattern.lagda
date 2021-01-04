\section{Patterns and Instantiations}

\hide{
\begin{code}
module Pattern where
\end{code}
}

\begin{code}
open import CoreLanguage
open import Thinning using (_⊑_; _∘_; ι; _I; _⟨term_; _⇒[_]_)
open import Data.Char using (Char)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (true; false)
open import Relation.Nullary using (does; _because_; proof; ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_×_; _,_)

open import Data.Maybe.Categorical using (monad)
open import Category.Monad.Indexed using (RawIMonad)
open import Level using (0ℓ)
open RawIMonad (monad {0ℓ})
\end{code}

\begin{code}
private
  variable
    δ : Scope
    γ : Scope

-- a pattern
data Pattern (γ : Scope) : Set where
  `      : Char → Pattern γ
  _∙_    : Pattern γ → Pattern γ → Pattern γ
  bind   : Pattern (suc γ) → Pattern γ
  place  : {δ : Scope} → δ ⊑ γ → Pattern γ
  ⊥      : Pattern γ

infixr 20 _∙_

-- ⊥ = ⊥ ∙ q = p ∙ ⊥ = bind ⊥

-- patterns are thinnable
_⟨pat_ : Pattern δ → (δ ⊑ γ) → Pattern γ
` x     ⟨pat θ = ` x
(s ∙ t) ⟨pat θ = (s ⟨pat θ) ∙ (t ⟨pat θ)
bind t  ⟨pat θ = bind (t ⟨pat (θ I))
place ϕ ⟨pat θ = place (ϕ ∘ θ)
⊥       ⟨pat θ = ⊥

private
  variable
    p : Pattern γ
    q : Pattern γ
    r : Pattern γ
    t : Pattern (suc γ)

data _-Env {γ : Scope} : Pattern γ → Set where
  `      : {c : Char} → (` c) -Env
  _∙_    : q -Env → r -Env → (q ∙ r) -Env
  bind   : t -Env → (bind t) -Env
  thing  : {θ : δ ⊑ γ} → Term lib const δ → (place θ) -Env

-- No maybe, just can't call it with incorrect args!
⟦_⟧env : (p : Pattern γ) → p -Env → Term lib const γ
⟦ ` a        ⟧env `           = ess (` a)
⟦ p ∙ q      ⟧env (e ∙ f)     = ess (⟦ p ⟧env e ∙ ⟦ q ⟧env f)
⟦ bind t     ⟧env (bind e)    = ess (bind (⟦ t ⟧env e))
⟦ place θ    ⟧env (thing t) = t ⟨term θ


{-
  THIS COULD BE NOT QUITE RIGHT!!!
  Need to come back and think about this

  So matching is defined inductively, working it's way down, matching
  the structures until it finally reaches 'places' where we check scopes
  before deciding if the term matches the place.

 ** should we be checking δ ≟ δ' ? or should we actually be looking for
 something like δ ⊑ δ'? **
-}
match : Term lib const δ → (p : Pattern γ) → Maybe (p -Env)
match (ess (` a)) (` c)       = just `
match (ess (s ∙ t)) (p ∙ q)   = do
                                  x ← match s p
                                  y ← match t q
                                  return (x ∙ y)
match (ess (bind t)) (bind p) = do
                                  x ← match t p
                                  return (bind x)
match {δ} {γ} t (place {δ'} θ) with δ ≟ δ'
... | .true because ofʸ refl  = just (thing t)
... | _                       = nothing
match _ _                     = nothing

private
  variable
    θ : δ ⊑ γ
 
data svar : Pattern γ → Scope → Set where
  ⋆    : {θ : δ ⊑ γ} → svar (place θ) δ -- ⋆ marks the spot
  _∙   : svar p γ → svar (p ∙ q) γ
  ∙_   : svar q γ → svar (p ∙ q) γ
  bind : svar t γ → svar (bind t) γ

-- for example, for some pattern
open import Thinning using (ε; _O; _I)
testPattern : Pattern 2
testPattern = (place (ε O I) ∙ place (ε I O)) ∙ bind (place (ε O O I) ∙ place (ε O I O))
-- we can refer to aspects of it structurally:
var1 : svar testPattern 1
var1 = (⋆ ∙) ∙

var2 : svar testPattern 1
var2 = (∙ ⋆) ∙

var3 : svar testPattern 1
var3 = ∙ bind (⋆ ∙)

var4 : svar testPattern 1
var4 = ∙ bind (∙ ⋆)

-- crucually, we can now look up terms in an environment
_‼_ : svar p δ → p -Env → Term lib const δ
⋆      ‼ thing x   = x
(v ∙)  ‼ (p ∙ q)   = v ‼ p
(∙ v)  ‼ (p ∙ q)   = v ‼ q
bind v ‼ bind t    = v ‼ t
\end{code}

\begin{code}
s-scope = Scope × (Pattern 0)

private
  variable
    p⁰ : Pattern 0
    γ' : Scope
    l : Lib
    d : Dir

Expr : s-scope → Lib → Dir → Scope → Set

data Expr-Lib-Const δ γ : Set where
  lib-const  : Lib-Const γ → Expr-Lib-Const δ γ
  _/_        : svar p⁰ γ' → γ' ⇒[ Expr (δ , p⁰) lib compu ] γ → Expr-Lib-Const δ γ

data Expr-Ess-Compu δ γ : Set where
  ess-compu  : Ess-Compu γ → Expr-Ess-Compu δ γ
  scvar      : Var δ → Expr-Ess-Compu δ γ

Expr (δ , p) ess const γ = Ess-Const γ
Expr (δ , p) ess compu γ = Expr-Ess-Compu δ γ
Expr (δ , p) lib const γ = Expr-Lib-Const δ γ
Expr (δ , p) lib compu γ = Lib-Compu γ

toExpr : Term l d γ → Expr (0 , ` '⊤') l d γ
toExpr {ess} {const} t = t
toExpr {lib} {compu} t = t
toExpr {ess} {compu} t = ess-compu t
toExpr {lib} {const} t = lib-const t
\end{code}

