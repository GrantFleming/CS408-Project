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

-- we can match a bunch of patterns if we wish
-- i deliberatly allow m ≠ n for the vectors here
-- we want to supply any list of inputs, if ther are not the same length
-- then there is no match
-- where we use this, we will not know for sure
match-all : Vec (Term lib const δ) m → (ps : Vec (Pattern γ) n) → Maybe (All _-Env ps)
match-all [] (_ ∷ _) = nothing
match-all (_ ∷ _) [] = nothing
match-all [] [] = just []
match-all (i ∷ ins) (p ∷ pats)
  = do
      e ← match i p
      es ← match-all ins pats
      just (e ∷ es)

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
s-scope = Scope × (Pattern 0)

private
  variable
    l : Lib
    d : Dir
    d' : Dir

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
    dvar   : Var δ → ecom δ p γ
  
  data lcom δ p γ where
    ess    : ecom δ p γ → lcom δ p γ
    _∷_    : lcon δ p γ → lcon δ p γ → lcom δ p γ
  
  Expr (δ , p) ess const γ = econ δ p γ
  Expr (δ , p) ess compu γ = ecom δ p γ
  Expr (δ , p) lib const γ = lcon δ p γ
  Expr (δ , p) lib compu γ = lcom δ p γ
  
  Expression : Scoped
  Expression γ = ∀ {δ} {p} {l} {d} → Expr (δ , p) l d γ

  -- expressions are thinnable on γ
  _⟨exp_ : Thinnable (Expr (δ , p) l d)
  
  _⟨exp_ {l = ess} {d = const} (` x)    θ = ` x
  _⟨exp_ {l = ess} {d = const} (s ∙ t)  θ = (s ⟨exp θ) ∙ (t ⟨exp θ)
  _⟨exp_ {l = ess} {d = const} (bind t) θ = bind (t ⟨exp (θ I))
  
  _⟨exp_ {l = ess} {d = compu} (var x)    θ  = var (x ⟨var θ)
  _⟨exp_ {l = ess} {d = compu} (elim e s) θ  = elim (e ⟨exp θ) (s ⟨exp θ)
  _⟨exp_ {l = ess} {d = compu} (dvar x)   θ  = dvar x
  
  _⟨exp_ {l = lib} {d = const} (ess x)   θ = ess (x ⟨exp θ)
  _⟨exp_ {l = lib} {d = const} (thunk x) θ = thunk (x ⟨exp θ)
  _⟨exp_ {l = lib} {d = const} (ξ / σ)   θ = ξ / (σ ⟨ θ)
    where
      -- had to inline ⟨sub for the termination checker
      _⟨_ : Thinnable (γ' ⇒[ (λ γ → lcom δ p γ) ]_)
      _⟨_  ε        θ' = ε
      _⟨_ (σ' -, x) θ' = (σ' ⟨ θ') -, (x ⟨exp θ')
  _⟨exp_ {l = lib} {d = compu} (ess x) θ  = ess (x ⟨exp θ)
  _⟨exp_ {l = lib} {d = compu} (t ∷ T) θ  = (t ⟨exp θ) ∷ (T ⟨exp θ)

  -- expressions are weakenable on γ
  _^exp : Weakenable (Expr (δ , p) l d)
  _^exp {δ} {p} {l} {d} = weaken {T = Expr (δ , p) l d} _⟨exp_

  -- but expressions are also thinnable on δ
  _⟨expδ_ : Thinnable (λ δ → Expr (δ , p) l d γ)
  
  _⟨expδ_ {l = ess} {d = const} (` x)    θ = ` x
  _⟨expδ_ {l = ess} {d = const} (s ∙ t)  θ = (s ⟨expδ θ) ∙ (t ⟨expδ θ)
  _⟨expδ_ {l = ess} {d = const} (bind x) θ = bind (x ⟨expδ θ)
  
  _⟨expδ_ {l = ess} {d = compu} (var x)    θ  = var x
  _⟨expδ_ {l = ess} {d = compu} (elim e s) θ  = elim (e ⟨expδ θ) (s ⟨expδ θ)
  _⟨expδ_ {l = ess} {d = compu} (dvar x)   θ  = dvar (x ⟨var θ)
  
  _⟨expδ_ {l = lib} {d = const} (ess x)   θ = ess (x ⟨expδ θ)
  _⟨expδ_ {l = lib} {d = const} (thunk x) θ = thunk (x ⟨expδ θ)
  _⟨expδ_ {l = lib} {d = const} (ξ / σ)   θ = ξ / (σ ⟨ θ)
    where
      -- had to inline ⟨sub for the termination checker
      _⟨_ : Thinnable  (λ δ → (γ' ⇒[ (λ γ → lcom δ p γ) ] γ))
      ε        ⟨ θ' = ε
      (σ' -, x) ⟨ θ' = (σ' ⟨ θ') -, (x ⟨expδ θ')
  
  _⟨expδ_ {l = lib} {d = compu} (ess x)  θ = ess (x ⟨expδ θ)
  _⟨expδ_ {l = lib} {d = compu} (t ∷ T) θ = (t ⟨expδ θ) ∷ (T ⟨expδ θ)

  -- expressions are also weakenable on δ
  _^expδ : Weakenable (λ δ → Expr (δ , p) l d γ)
  _^expδ {p} {l} {d} {γ}  = weaken {T = λ δ → Expr (δ , p) l d γ} _⟨expδ_

  -- substituting expressions is weakenable
  _^/exp : Weakenable
            (γ ⇒[ Expr (δ , p) l d ]_)
  _^/exp {δ = δ} {p = p} {l = l} {d = d}  = ^sub {T = Expr (δ , p) l d}  _⟨exp_

  -- Environments for elimination targets
  -- things in the environment need to be synthesizable for elim rules
  e-Env : Scope → Scope → Set
  e-Env δ γ = δ ⇒[ Term lib compu ] γ

  -- because terms are thinnable, e-Envs are thinnable on γ
  _⟨eenv_ : Thinnable (e-Env δ)
  e ⟨eenv θ = ⟨sub _⟨term_ e θ

  -- therefore weakenable
  _^eenv : Weakenable (e-Env δ) 
  _^eenv = weaken _⟨eenv_

  ↠_ : lcom δ p γ → lcon δ p γ
  ↠ (ess x) = thunk x
  ↠ (t ∷ T) = t

               -- δ p was originally 0 , ` '⊤'
  toExpr : Term l d γ → Expr (δ , p) l d γ
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
  _//_ :  Expr (δ , p) l d γ' → γ' ⇒[ Expr (δ , p) lib compu ] γ → Expr (δ , p) lib d γ
  _//_ {l = ess} {d = const} (` x)       σ = ess (` x)
  _//_ {l = ess} {d = const} (s ∙ t)     σ = ess ((s // σ) ∙ (t // σ))
  _//_ {l = ess} {d = const} (bind t)    σ = ess (bind (t // ((σ ^/exp) -, ess (var ze))))
  
  _//_ {δ} {p} {ess} {compu} (var v)     σ = lookup (Expr (δ , p) lib compu) σ v
  _//_ {l = ess} {d = compu} (elim e s) σ = ess (elim (e // σ) (s // σ))
  _//_ {l = ess} {d = compu} (dvar x)   σ = ess (dvar x)
  
  _//_ {l = lib} {d = const} (ess x)     σ = x // σ
  _//_ {l = lib} {d = const} (thunk x)   σ = ↠ (x // σ)
  _//_ {l = lib} {d = const} (ξ / σ')    σ = ξ / (σ' ∘` σ)
    where
    -- had to inline this composition here to shut the termination checker up
    _∘`_ : Composable (_⇒[ lcom δ p ]_)
    ε ∘`          two = ε
    (one -, x) ∘` two = (one ∘` two) -, (x // two)
  
  _//_ {l = lib} {d = compu} (ess x)     σ = x // σ
  _//_ {l = lib} {d = compu} (t ∷ T)     σ = (t // σ) ∷ (T // σ)


  -- TO DO - get the termination checker to see that this is terminating
  {-# TERMINATING #-}
  toTerm  : p -Env → e-Env δ γ → Expr (δ , p) l d γ → Term lib d γ
  toTerm {l = ess} {d = const} penv eenv (` x)        = ess (` x)
  toTerm {_} {l = ess} {d = const} penv eenv (s ∙ t)  = ess ((toTerm penv eenv s) ∙ (toTerm penv eenv t))
  toTerm {_} {l = ess} {d = const} penv eenv (bind t) = ess (bind (toTerm penv (eenv ^eenv) t))
  
  toTerm {_} {l = ess} {d = compu} penv eenv (var x)    = ess (var x)
  toTerm {_} {l = ess} {d = compu} penv eenv (elim e s) = ess (elim (toTerm penv eenv e) (toTerm penv eenv s))
  toTerm {_} {l = ess} {d = compu} penv eenv (dvar v)   = lookup (Term lib compu) eenv v

  toTerm {_} {l = lib} {d = const} penv eenv (ess x)   = toTerm penv eenv x
  toTerm {_} {l = lib} {d = const} penv eenv (thunk x) = ↠↠ (toTerm penv eenv x)
  toTerm {_} {l = lib} {d = const} penv eenv (ξ / σ) =  toTerm penv eenv (toExpr (ξ ‼ penv) // σ)
  
  toTerm {_} {l = lib} {d = compu} penv eenv (ess x) = toTerm penv eenv x
  toTerm {_} {l = lib} {d = compu} penv eenv (t ∷ T) = toTerm penv eenv t ∷ toTerm penv eenv T
\end{code}

