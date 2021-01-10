\section{Patterns and Instantiations}

\hide{
\begin{code}
module Pattern where
\end{code}
}

\begin{code}
open import CoreLanguage
open import Thinning using (_⊑_; _∘_; ι; _I; _O; _⟨term_; _⇒[_]_; ↑; Scoped; Thinnable; Weakenable; weaken)
open import Data.Char using (Char) renaming (_≟_ to _is_)
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
_⟨pat_ : Thinnable Pattern
` x     ⟨pat θ = ` x
(s ∙ t) ⟨pat θ = (s ⟨pat θ) ∙ (t ⟨pat θ)
bind t  ⟨pat θ = bind (t ⟨pat (θ I))
place ϕ ⟨pat θ = place (ϕ ∘ θ)
⊥       ⟨pat θ = ⊥

-- and can therefore be weakened
_^pat : Weakenable Pattern
_^pat = weaken _⟨pat_

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

-- environments are thinnable by thinning the patterns
_⟨env_ : {p : Pattern δ} → p -Env → (θ : δ ⊑ γ) → ((p ⟨pat θ) -Env)
`       ⟨env θ  = `
(s ∙ t) ⟨env θ  = (s ⟨env θ) ∙ (t ⟨env θ)
bind t  ⟨env θ  = bind (t ⟨env (θ I))
thing x ⟨env θ  = thing x

-- and can be weakened
_^env : p -Env → (p ^pat) -Env
_^env e = e ⟨env ↑

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
match (ess (` a)) (` c) with a is c
... | true because ofʸ refl = just `
... | _                     = nothing
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
    γ' : Scope

-- γ ⊑ γ⁺ is the scope extension so far in the pattern

data svar : Pattern γ → Scope → Set where
  ⋆    : {θ : δ ⊑ γ} → svar (place θ) δ -- ⋆ marks the spot
  _∙   : svar p δ → svar (p ∙ q) δ
  ∙_   : svar q δ → svar (p ∙ q) δ
  bind : svar q δ → svar (bind q) δ

-- svar is thinnable (but slightly differently so we can't use "Thinnable"
_⟨svar_ : ∀ {γ} {p : Pattern γ} {δ} → svar p δ → (θ : γ ⊑ γ') → svar {γ'} (p ⟨pat θ ) δ
⋆ {_} {_} {ϕ}  ⟨svar θ = ⋆ {_} {_} {ϕ ∘ θ}
(v ∙)  ⟨svar θ = (v ⟨svar θ) ∙
(∙ v)  ⟨svar θ = ∙ (v ⟨svar θ)
bind v ⟨svar θ = bind (v ⟨svar (θ I))

-- for example, for some pattern
open import Thinning using (ε; _O; _I)
testPattern : Pattern 2
testPattern = (place (ε O I) ∙ place (ε I O)) ∙ bind (place (ε O O I) ∙ place (ε I I I))
-- we can refer to aspects of it structurally:
var1 : svar testPattern 1
var1 = (⋆ ∙) ∙

var2 : svar testPattern 1
var2 = (∙ ⋆) ∙

var3 : svar testPattern 1
var3 = ∙ bind (⋆ ∙)

var4 : svar testPattern 3
var4 = ∙ bind (∙ ⋆)

-- crucually, we can now look up terms in an environment
_‼_ : svar p δ → p -Env → Term lib const δ
⋆      ‼ thing x   = x
(v ∙)  ‼ (p ∙ q)   = v ‼ p
(∙ v)  ‼ (p ∙ q)   = v ‼ q
bind v ‼ bind t    = v ‼ t

{-
  
  TESTING!!!

-}

-- λ f → λ x → x y
tm : Term lib const 0
tm = ess (ess (` 'λ') ∙ ess (bind (ess ((ess (` 'λ')) ∙ (ess (bind (thunk (elim (ess (var (su ze))) (thunk (var ze))))))))))

open import Thinning using (ε; _O; _I; ι)

pat : Pattern 0
pat = ` 'λ' ∙ bind (` 'λ' ∙ bind (place (ε O I)))

result = match tm pat

myvar : svar pat 1
myvar = ∙ bind (∙ bind ⋆)

mlook : svar p δ → Maybe (p -Env) → Maybe (Term lib const δ)
mlook v nothing = nothing
mlook v (just x) = just (v ‼ x)

otherresult = mlook myvar result

\end{code}

\begin{code}
s-scope = Scope × (Pattern 0)

private
  variable
    l : Lib
    d : Dir

module Expression where

  Expr : s-scope → Lib → Dir → Scoped
  
  data econ (δ : Scope) (p : Pattern 0) (γ : Scope) : Set
  data lcon (δ : Scope) (p : Pattern 0) (γ : Scope) : Set
  data ecom (δ : Scope) (p : Pattern 0) (γ : Scope) : Set
  data lcom (δ : Scope) (p : Pattern 0) (γ : Scope) : Set
  
  data econ δ p γ where
    `      : Char → econ δ p γ
    _∙_   : lcon δ p γ → lcon δ p γ → econ δ p γ
    bind   : lcon δ p (suc γ) → econ δ p γ
  
  infixr 20 _∙_ 
  
  data lcon δ p γ where
    ess    : econ δ p γ → lcon δ p γ
    thunk  : ecom δ p γ → lcon δ p γ
    _/_    : svar p γ' → γ' ⇒[ Expr (δ , p) lib compu ] γ → lcon δ p γ
    
  
  data ecom δ p γ where
    var    : Var γ → ecom δ p γ
    elim   : lcom δ p γ → lcon δ p γ → ecom δ p γ
  
  data lcom δ p γ where
    ess    : ecom δ p γ → lcom δ p γ
    _∷_    : lcon δ p γ → lcon δ p γ → lcom δ p γ
  
  Expr (δ , p) ess const γ = econ δ p γ
  Expr (δ , p) ess compu γ = ecom δ p γ
  Expr (δ , p) lib const γ = lcon δ p γ
  Expr (δ , p) lib compu γ = lcom δ p γ
  
  Expression : Scoped
  Expression γ = ∀ {δ} {p} {l} {d} → Expr (δ , p) l d γ
  
  toExpr : Term l d γ → Expr (0 , ` '⊤') l d γ
  toExpr {ess} {const} (` x)    = ` x
  toExpr {ess} {const} (s ∙ t)  = (toExpr s) ∙ (toExpr t)
  toExpr {ess} {const} (bind x) = bind (toExpr x)
  
  toExpr {lib} {compu} (ess x) = ess (toExpr x)
  toExpr {lib} {compu} (t ∷ T) = (toExpr t) ∷ (toExpr T)
  
  toExpr {ess} {compu} (var x)    = var x
  toExpr {ess} {compu} (elim e s) = elim (toExpr e) (toExpr s)
  
  toExpr {lib} {const} (ess x)   = ess   (toExpr x)
  toExpr {lib} {const} (thunk x) = thunk (toExpr x)
\end{code}

