\section{Patterns and Instantiations}

\hide{
\begin{code}
module Pattern where
\end{code}
}

\begin{code}
open import CoreLanguage renaming (↠ to ↠↠)
open import Thinning hiding (⊥)
open import Data.Char using (Char) renaming (_≟_ to _is_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Bool using (true; false)
open import Relation.Nullary using (does; _because_; proof; ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
\end{code}

\begin{code}
private
  variable
    δ : Scope
    γ : Scope
    n : ℕ
    m : ℕ

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
                                  just (x ∙ y)
match (ess (bind t)) (bind p) = do
                                  x ← match t p
                                  just (bind x)
match {δ} {γ} t (place {δ'} θ) with δ ≟ δ'
... | .true because ofʸ refl  = just (thing t)
... | _                       = nothing
match _ _                     = nothing

private
  variable
    θ : δ ⊑ γ
    γ' : Scope
    γ'' : Scope

-- γ ⊑ γ⁺ is the scope extension so far in the pattern

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

-- we can also get the term back from the pattern and the environment
termFrom : (p : Pattern γ) → p -Env → Term lib const γ
termFrom (` x) `              = ess (` x)
termFrom (p ∙ p₁) (e ∙ e₁)    = ess (termFrom p e ∙ termFrom p₁ e₁)
termFrom (bind p) (bind e)    = ess (bind (termFrom p e))
termFrom (place θ) (thing x₁) = x₁ ⟨term θ
termFrom ⊥ ()

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
mlook v nothing  =  nothing
mlook v (just x) = just (v ‼ x)

otherresult = mlook myvar result

\end{code}

\begin{code}
private
  variable
    l : Lib
    d : Dir
    d' : Dir

module Expression where

  Expr : Pattern 0 → Lib → Dir → Scoped
  
  data econ (p : Pattern 0) (γ : Scope) : Set
  data lcon (p : Pattern 0) (γ : Scope) : Set
  data ecom (p : Pattern 0) (γ : Scope) : Set
  data lcom (p : Pattern 0) (γ : Scope) : Set
  
  data econ p γ where
    `      : Char → econ p γ
    _∙_   : lcon p γ → lcon p γ → econ p γ
    bind   : lcon p (suc γ) → econ p γ
  
  infixr 20 _∙_ 
  
  data lcon p γ where
    ess    : econ p γ → lcon p γ
    thunk  : ecom p γ → lcon p γ
    _/_    : svar p γ' → γ' ⇒[ Expr p lib compu ] γ → lcon p γ
    
  
  data ecom p γ where
    var    : Var γ → ecom p γ
    elim   : lcom p γ → lcon p γ → ecom p γ
  
  data lcom p γ where
    ess    : ecom p γ → lcom p γ
    _∷_    : lcon p γ → lcon p γ → lcom p γ
  
  Expr p ess const γ = econ p γ
  Expr p ess compu γ = ecom p γ
  Expr p lib const γ = lcon p γ
  Expr p lib compu γ = lcom p γ
  
  Expression : Scoped
  Expression γ = ∀ {p} {l} {d} → Expr p l d γ

  -- expressions are thinnable on γ
  _⟨exp_ : Thinnable (Expr p l d)
  
  _⟨exp_ {l = ess} {d = const} (` x)    θ = ` x
  _⟨exp_ {l = ess} {d = const} (s ∙ t)  θ = (s ⟨exp θ) ∙ (t ⟨exp θ)
  _⟨exp_ {l = ess} {d = const} (bind t) θ = bind (t ⟨exp (θ I))
  
  _⟨exp_ {l = ess} {d = compu} (var x)    θ  = var (x ⟨var θ)
  _⟨exp_ {l = ess} {d = compu} (elim e s) θ  = elim (e ⟨exp θ) (s ⟨exp θ)
  
  _⟨exp_ {l = lib} {d = const} (ess x)   θ = ess (x ⟨exp θ)
  _⟨exp_ {l = lib} {d = const} (thunk x) θ = thunk (x ⟨exp θ)
  _⟨exp_ {l = lib} {d = const} (ξ / σ)   θ = ξ / (σ ⟨ θ)
    where
      -- had to inline ⟨sub for the termination checker
      _⟨_ : Thinnable (γ' ⇒[ (λ γ → lcom p γ) ]_)
      _⟨_  ε        θ' = ε
      _⟨_ (σ' -, x) θ' = (σ' ⟨ θ') -, (x ⟨exp θ')
  _⟨exp_ {l = lib} {d = compu} (ess x) θ  = ess (x ⟨exp θ)
  _⟨exp_ {l = lib} {d = compu} (t ∷ T) θ  = (t ⟨exp θ) ∷ (T ⟨exp θ)

  -- expressions are weakenable on γ
  _^exp : Weakenable (Expr p l d)
  _^exp {p} {l} {d} = weaken {T = Expr p l d} _⟨exp_

  -- substituting expressions is weakenable
  _^/exp : Weakenable
            (γ ⇒[ Expr p l d ]_)
  _^/exp {p = p} {l = l} {d = d}  = ^sub {T = Expr p l d}  _⟨exp_

  ↠_ : lcom p γ → lcon p γ
  ↠ (ess x) = thunk x
  ↠ (t ∷ T) = t

               -- δ p was originally 0 , ` '⊤'
  toExpr : Term l d γ → Expr p l d γ
  toExpr {ess} {const} (` x)    = ` x
  toExpr {ess} {const} (s ∙ t)  = (toExpr s) ∙ (toExpr t)
  toExpr {ess} {const} (bind x) = bind (toExpr x)
  
  toExpr {lib} {compu} (ess x) = ess (toExpr x)
  toExpr {lib} {compu} (t ∷ T) = (toExpr t) ∷ (toExpr T)
  
  toExpr {ess} {compu} (var x)    = var x
  toExpr {ess} {compu} (elim e s) = elim (toExpr e) (toExpr s)
  
  toExpr {lib} {const} (ess x)   = ess   (toExpr x)
  toExpr {lib} {const} (thunk x) = thunk (toExpr x)

  

    -- actually performing the lcon substitution
  _//_ :  Expr p l d γ' → γ' ⇒[ Expr p lib compu ] γ → Expr p lib d γ
  _//_ {l = ess} {d = const} (` x)       σ = ess (` x)
  _//_ {l = ess} {d = const} (s ∙ t)     σ = ess ((s // σ) ∙ (t // σ))
  _//_ {l = ess} {d = const} (bind t)    σ = ess (bind (t // ((σ ^/exp) -, ess (var ze))))
  
  _//_ {p} {ess} {compu} (var v)     σ = lookup (Expr p lib compu) σ v
  _//_ {l = ess} {d = compu} (elim e s) σ = ess (elim (e // σ) (s // σ))
    
  _//_ {l = lib} {d = const} (ess x)     σ = x // σ
  _//_ {l = lib} {d = const} (thunk x)   σ = ↠ (x // σ)
  _//_ {l = lib} {d = const} (ξ / σ')    σ = ξ / (σ' ∘` σ)
    where
    -- had to inline this composition here to shut the termination checker up
    _∘`_ : Composable (_⇒[ lcom p ]_)
    ε ∘`          two = ε
    (one -, x) ∘` two = (one ∘` two) -, (x // two)
  
  _//_ {l = lib} {d = compu} (ess x)     σ = x // σ
  _//_ {l = lib} {d = compu} (t ∷ T)     σ = (t // σ) ∷ (T // σ)


  -- TO DO - get the termination checker to see that this is terminating
  {-# TERMINATING #-}
  toTerm  : p -Env → Expr p l d γ → Term lib d γ
  toTerm {l = ess} {d = const} penv (` x)    = ess (` x)
  toTerm {l = ess} {d = const} penv (s ∙ t)  = ess ((toTerm penv s) ∙ (toTerm penv t))
  toTerm {l = ess} {d = const} penv (bind t) = ess (bind (toTerm penv t))
  
  toTerm {l = ess} {d = compu} penv (var x)    = ess (var x)
  toTerm {l = ess} {d = compu} penv (elim e s) = ess (elim (toTerm penv e) (toTerm penv s))

  toTerm {l = lib} {d = const} penv (ess x)   = toTerm penv x
  toTerm {l = lib} {d = const} penv (thunk x) = ↠↠ (toTerm penv x)
  toTerm {l = lib} {d = const} penv (ξ / σ) =  toTerm penv (toExpr (ξ ‼ penv) // σ)
  
  toTerm {l = lib} {d = compu} penv (ess x) = toTerm penv x
  toTerm {l = lib} {d = compu} penv (t ∷ T) = toTerm penv t ∷ toTerm penv T


\end{code}

