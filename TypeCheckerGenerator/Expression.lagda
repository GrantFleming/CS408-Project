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
    d : Dir
    d' : Dir

Expr : Pattern δ → Dir → Scoped

data con (p : Pattern δ) (γ : Scope) : Set
data com (p : Pattern δ) (γ : Scope) : Set

data con p γ where
  `      : Char → con p γ
  _∙_    : con p γ → con p γ → con p γ
  bind   : con p (suc γ) → con p γ
  thunk  : com p γ → con p γ
  _/_    : svar p γ' → γ' ⇒[ Expr p compu ] γ → con p γ

infixr 20 _∙_ 
  
data com p γ where
  var    : Var γ → com p γ
  elim   : com p γ → con p γ → com p γ
  _∷_    : con p γ → con p γ → com p γ


Expr p const γ = con p γ
Expr p compu γ = com p γ

{-Expression : Scoped
Expression γ = ∀ {δ} {p : Pattern δ} {d} → Expr p d γ-}

-- expressions are thinnable on γ
_⟨exp_ : Thinnable (Expr p d)

_⟨exp_ {d = const} (` x)    θ = ` x
_⟨exp_ {d = const} (s ∙ t)  θ = (s ⟨exp θ) ∙ (t ⟨exp θ)
_⟨exp_ {d = const} (bind t) θ = bind (t ⟨exp (θ I))
_⟨exp_ {d = const} (thunk x) θ = thunk (x ⟨exp θ)
_⟨exp_ {d = const} (ξ / σ)   θ = ξ / (σ ⟨ θ)
  where
    -- had to inline ⟨sub for the termination checker
    _⟨_ : Thinnable (γ' ⇒[ (λ γ → com p γ) ]_)
    _⟨_  ε        θ' = ε
    _⟨_ (σ' -, x) θ' = (σ' ⟨ θ') -, (x ⟨exp θ')

_⟨exp_ {d = compu} (var x)    θ  = var (x ⟨var θ)
_⟨exp_ {d = compu} (elim e s) θ  = elim (e ⟨exp θ) (s ⟨exp θ)
_⟨exp_ {d = compu} (t ∷ T) θ  = (t ⟨exp θ) ∷ (T ⟨exp θ)

-- expressions are weakenable on γ
_^exp : Weakenable (Expr p d)
_^exp {p = p} {d = d} = weaken {T = Expr p d} _⟨exp_

-- substituting expressions is weakenable
_^/exp : Weakenable
          (γ ⇒[ Expr p d ]_)
_^/exp {p = p} {d = d}  = ^sub {T = Expr p d}  _⟨exp_


↠_ : com p γ → con p γ
↠ (t ∷ T) = t
↠  x      = thunk x

  -- actually performing the lcon substitution
_//_ :  Expr p d γ' → γ' ⇒[ Expr p compu ] γ → Expr p d γ
_//_ {d = const} (` x)       σ = ` x
_//_ {d = const} (s ∙ t)     σ = (s // σ) ∙ (t // σ)
_//_ {d = const} (bind t)    σ = bind (t // ((σ ^/exp) -, var ze))
_//_ {d = const} (thunk x)   σ = ↠ (x // σ)
_//_ {d = const} (ξ / σ')    σ = ξ / (σ' ∘` σ)
  where
  -- had to inline this composition here to shut the termination checker up
  _∘`_ : Composable (_⇒[ com p ]_)
  ε ∘`          two = ε
  (one -, x) ∘` two = (one ∘` two) -, (x // two)

_//_ {p = p} {d = compu} (var v)        σ = lookup (Expr p compu) σ v
_//_ {d = compu} (elim e s) σ = elim (e // σ) (s // σ)
_//_ {d = compu} (t ∷ T)     σ = (t // σ) ∷ (T // σ)

idexpr : γ ⇒[ Expr p compu ] γ
idexpr {zero}          = ε
idexpr {suc γ} {p = p} = ^sub {T = Expr p compu} _⟨exp_ idexpr -, var (fromNum γ)


_⊗expr_ : Expr p d δ → (γ : Scope) → Expr (γ ⊗ p) d (γ + δ)

-- we can 'open' a substitution of expressions
_⊗sub_ : δ ⇒[ Expr p compu ] γ → (δ' : Scope) → (δ' + δ) ⇒[ Expr (δ' ⊗  p) compu ] (δ' + γ)
_⊗sub_ {p = p} {γ = γ} ε δ' = ⟨sub {T = Expr (δ' ⊗ p) compu} _⟨exp_ (idexpr {δ'}) (δ' ◃ γ)
(σ -, x) ⊗sub δ' = (σ ⊗sub δ') -, (x ⊗expr δ')

-- so we can 'open up' an expression
_⊗expr_ {d = const} (` x)      γ  = ` x
_⊗expr_ {d = const} (s ∙ t)    γ  = (s ⊗expr γ) ∙ (t ⊗expr γ)
_⊗expr_ {d = const} (bind x)   γ  = bind (x ⊗expr γ)
_⊗expr_ {d = const} (thunk x)  γ  = thunk (x ⊗expr γ)
_⊗expr_ {d = const} {δ = δ} (ξ / σ)    γ  = (ξ ⊗svar γ) / (σ ⊗sub γ)
_⊗expr_ {d = compu} (var x)    γ  = var (x ⊗var γ)
_⊗expr_ {d = compu} (elim e s) γ  = elim (e ⊗expr γ) (s ⊗expr γ)
_⊗expr_ {d = compu} (t ∷ T)    γ  = (t ⊗expr γ) ∷ (T ⊗expr γ)

toTerm  : (γ ⊗ p) -Env → Expr p d γ' → Term d (γ + γ')
toTerm {d = const} penv (` x)    = ` x
toTerm {d = const} penv (s ∙ t)  = (toTerm penv s) ∙ (toTerm penv t)
toTerm {d = const} penv (bind t) = bind  (toTerm penv t) 
toTerm {d = const} penv (thunk x) = ↠↠ (toTerm penv x)
toTerm {γ = γ} {d = const} {γ' = γ'} penv (ξ / σ)
  = let σpenv = helper σ penv in
    let thingy = ⟨sub {T = Term compu} _⟨term_ id (γ ◃ γ') in
    (ξ ‼ penv) /term ((thingy ++sub σpenv))
    where
      helper : ∀ {γ} → δ' ⇒[ Expr p d ] γ' → ((γ ⊗ p) -Env)  → δ' ⇒[ Term d ] (γ + γ')
      helper ε env = ε
      helper (σ -, x) env = helper σ env -, toTerm env x
toTerm {γ = γ} {d = compu} {γ' = γ'} penv (var x) = var (x ⟨var (γ ▹ γ'))
toTerm {d = compu} penv (elim e s) = elim (toTerm penv e) (toTerm penv s)
toTerm {d = compu} penv (t ∷ T) = toTerm penv t ∷ toTerm penv T
\end{code}
