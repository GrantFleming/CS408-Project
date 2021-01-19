\section{Expressions}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Expression where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage renaming (↠ to ↠↠)
open import Pattern using (Pattern; _-Env; svar; _⊗_; _⊗var_; _⊗svar_; _‼_)
open import Thinning
open import Substitution
open import TermSubstitution
open import Composition
open import Data.Char using (Char)
open import Data.Nat using (zero; suc; _+_)
open import BwdVec
\end{code}
}

\begin{code}
private
  variable
    δ : Scope
    δ' : Scope
    γ : Scope
    p : Pattern γ
    γ' : Scope
    l : Lib
    d : Dir
    d' : Dir

Expr : Pattern δ → Lib → Dir → Scoped

data econ (p : Pattern δ) (γ : Scope) : Set
data lcon (p : Pattern δ) (γ : Scope) : Set
data ecom (p : Pattern δ) (γ : Scope) : Set
data lcom (p : Pattern δ) (γ : Scope) : Set

data econ p γ where
  `      : Char → econ p γ
  _∙_    : lcon p γ → lcon p γ → econ p γ
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

{-Expression : Scoped
Expression γ = ∀ {δ} {p : Pattern δ} {l} {d} → Expr p l d γ-}

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
_^exp {p = p} {l = l} {d = d} = weaken {T = Expr p l d} _⟨exp_

-- substituting expressions is weakenable
_^/exp : Weakenable
          (γ ⇒[ Expr p l d ]_)
_^/exp {p = p} {l = l} {d = d}  = ^sub {T = Expr p l d}  _⟨exp_


↠_ : lcom p γ → lcon p γ
↠ (ess x) = thunk x
↠ (t ∷ T) = t

  -- actually performing the lcon substitution
_//_ :  Expr p l d γ' → γ' ⇒[ Expr p lib compu ] γ → Expr p lib d γ
_//_ {l = ess} {d = const} (` x)       σ = ess (` x)
_//_ {l = ess} {d = const} (s ∙ t)     σ = ess ((s // σ) ∙ (t // σ))
_//_ {l = ess} {d = const} (bind t)    σ = ess (bind (t // ((σ ^/exp) -, ess (var ze))))

_//_ {p = p} {l = ess} {d = compu} (var v)        σ = lookup (Expr p lib compu) σ v
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

idexpr : γ ⇒[ Expr p lib compu ] γ
idexpr {zero}          = ε
idexpr {suc γ} {p = p} = ^sub {T = Expr p lib compu} _⟨exp_ idexpr -, ess (var (fromNum γ))


_⊗expr_ : Expr p l d δ → (γ : Scope) → Expr (γ ⊗ p) l d (γ + δ)

-- we can 'open' a substitution of expressions
_⊗sub_ : δ ⇒[ Expr p lib compu ] γ → (δ' : Scope) → (δ' + δ) ⇒[ Expr (δ' ⊗  p) lib compu ] (δ' + γ)
_⊗sub_ {p = p} {γ = γ} ε δ' = ⟨sub {T = Expr (δ' ⊗ p) lib compu} _⟨exp_ (idexpr {δ'}) (δ' ◃ γ)
(σ -, x) ⊗sub δ' = (σ ⊗sub δ') -, (x ⊗expr δ')

-- so we can 'open up' an expression
_⊗expr_ {l = ess} {d = const} (` x)      γ  = ` x
_⊗expr_ {l = ess} {d = const} (s ∙ t)    γ  = (s ⊗expr γ) ∙ (t ⊗expr γ)
_⊗expr_ {l = ess} {d = const} (bind x)   γ  = bind (x ⊗expr γ)
_⊗expr_ {l = ess} {d = compu} (var x)    γ  = var (x ⊗var γ)
_⊗expr_ {l = ess} {d = compu} (elim e s) γ  = elim (e ⊗expr γ) (s ⊗expr γ)
_⊗expr_ {l = lib} {d = const} (ess x)    γ  = ess (x ⊗expr γ)
_⊗expr_ {l = lib} {d = const} (thunk x)  γ  = thunk (x ⊗expr γ)
_⊗expr_ {l = lib} {d = const} {δ = δ} (ξ / σ)    γ  = (ξ ⊗svar γ) / (σ ⊗sub γ)
_⊗expr_ {l = lib} {d = compu} (ess x)    γ  = ess (x ⊗expr γ)
_⊗expr_ {l = lib} {d = compu} (t ∷ T)    γ  = (t ⊗expr γ) ∷ (T ⊗expr γ)

toTerm  : (γ ⊗ p) -Env → Expr p l d γ' → Term lib d (γ + γ')

toTerm {l = ess} {d = const} penv (` x)    = ess (` x)
toTerm {l = ess} {d = const} penv (s ∙ t)  = ess ((toTerm penv s) ∙ (toTerm penv t))
toTerm {γ = γ} {l = ess} {d = const} {γ' = γ'} penv (bind t)
  = ess (bind  (toTerm penv t) {-(subst Lib-Const (+-suc γ γ') ((toTerm penv t)))-})

toTerm {γ = γ} {l = ess} {d = compu} {γ' = γ'} penv (var x) = ess (var (x ⟨var (γ ▹ γ')))
toTerm {l = ess} {d = compu} penv (elim e s) = ess (elim (toTerm penv e) (toTerm penv s))

toTerm {l = lib} {d = const} penv (ess x)   = toTerm penv x
toTerm {l = lib} {d = const} penv (thunk x) = ↠↠ (toTerm penv x)
toTerm {γ = γ} {l = lib} {d = const} {γ' = γ'} penv (ξ / σ)
  = let σpenv = helper σ penv in
    let thingy = ⟨sub {T = Term lib compu} _⟨term_ id (γ ◃ γ') in
    (ξ ‼ penv) /term ((thingy ++sub σpenv))
    where
      helper : ∀ {γ} → δ' ⇒[ Expr p l d ] γ' → ((γ ⊗ p) -Env)  → δ' ⇒[ Term lib d ] (γ + γ')
      helper ε env = ε
      helper (σ -, x) env = helper σ env -, toTerm env x
    
toTerm {l = lib} {d = compu} penv (ess x) = toTerm penv x
toTerm {l = lib} {d = compu} penv (t ∷ T) = toTerm penv t ∷ toTerm penv T
\end{code}
