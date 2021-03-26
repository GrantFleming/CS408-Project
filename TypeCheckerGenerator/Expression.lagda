\section{Expressions}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Expression where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Pattern using
  (Pattern; _-Env; svar; _⊗_; _⊗var_; _⊗svar_; _‼_)
open import Thinning hiding (_++_)
open import Substitution
open import TermSubstitution
open import Composition
open import Data.String using (String)
open import Data.Nat using (zero; suc; _+_)
open import BwdVec hiding (map)
\end{code}
}

\hide{
\begin{code}
private
  variable
    δ : Scope
    δ' : Scope
    γ : Scope
    p : Pattern γ
    q : Pattern γ
    γ' : Scope
    d : Dir
    d' : Dir
\end{code}
}

Expressions allow us to define a way that we might construct a term from a
pattern that represents something that we trust. For example, if the expression
is showing how one might build the required term as the output of some
type-synthesis rule for elimination, what is trusted might be the type of the
target and whatever we learn to trust in the premises. These trusted patterns
contain places that sculpt out component parts in a piece of matched syntax
and allow us to use these component parts in constructing a new term.

Expressions mirror the structure of terms except that they include the option
to reference some place in a pattern and instantiate it with some substitution
of its free variables. This means that we might build a term based on some
piece of syntax that we do not yet have until the pattern is later matched.

\begin{code}
data Con (p : Pattern δ) (γ : Scope) : Set
data Com (p : Pattern δ) (γ : Scope) : Set

data Con p γ where
  `      : String → Con p γ
  _∙_    : Con p γ → Con p γ → Con p γ
  bind   : Con p (suc γ) → Con p γ
  thunk  : Com p γ → Con p γ
  _/_    : svar p γ' → γ' ⇒[ Com p ] γ → Con p γ
  
data Com p γ where
  var    : Var γ → Com p γ
  elim   : Com p γ → Con p γ → Com p γ
  _∷_    : Con p γ → Con p γ → Com p γ

Expr : Pattern δ → Dir → Scoped
Expr p const γ = Con p γ
Expr p compu γ = Com p γ
\end{code}
\hide{
\begin{code}
infixr 20 _∙_
_⟨exp_   : Thinnable (Expr p d)
_⟨exp_ {d = const} (` x)    θ = ` x
_⟨exp_ {d = const} (s ∙ t)  θ = (s ⟨exp θ) ∙ (t ⟨exp θ)
_⟨exp_ {d = const} (bind t) θ = bind (t ⟨exp (θ I))
_⟨exp_ {d = const} (thunk x) θ = thunk (x ⟨exp θ)
_⟨exp_ {d = const} (ξ / σ)   θ = ξ / (σ ⟨ θ)
  where
    -- had to inline ⟨sub for the termination checker
    _⟨_ : Thinnable (γ' ⇒[ (λ γ → Com p γ) ]_)
    _⟨_  ε        θ' = ε
    _⟨_ (σ' -, x) θ' = (σ' ⟨ θ') -, (x ⟨exp θ')

_⟨exp_ {d = compu} (var x)    θ  = var (x ⟨var θ)
_⟨exp_ {d = compu} (elim e s) θ  = elim (e ⟨exp θ) (s ⟨exp θ)
_⟨exp_ {d = compu} (t ∷ T) θ  = (t ⟨exp θ) ∷ (T ⟨exp θ)

_^exp    : Weakenable (Expr p d)
_^exp {p = p} {d = d} = weaken {T = Expr p d} _⟨exp_

_^/exp   : Weakenable (γ ⇒[ Expr p d ]_)
_^/exp {p = p} {d = d}  = ^sub {T = Expr p d}  _⟨exp_

idexpr : γ ⇒[ Expr p compu ] γ
idexpr {zero}          = ε
idexpr {suc γ} {p = p}
  = ^sub {T = Expr p compu} _⟨exp_ idexpr -, var (fromNum γ)

_⊗expr_  : (γ : Scope) → Expr p d δ → Expr (γ ⊗ p) d (γ + δ)
_⊗sub_ : (δ' : Scope) →
         δ ⇒[ Expr p compu ] γ →
         (δ' + δ) ⇒[ Expr (δ' ⊗  p) compu ] (δ' + γ)

_⊗expr_ {d = const} γ (` x)       = ` x
_⊗expr_ {d = const} γ (s ∙ t)     = (γ ⊗expr s) ∙ (γ ⊗expr t)
_⊗expr_ {d = const} γ (bind x)    = bind (γ ⊗expr x)
_⊗expr_ {d = const} γ (thunk x)   = thunk (γ ⊗expr x)
_⊗expr_ {d = const} γ (ξ / σ)     = (γ ⊗svar ξ) / (γ ⊗sub σ)
_⊗expr_ {d = compu} γ (var x)     = var (γ ⊗var x)
_⊗expr_ {d = compu} γ (elim e s)  = elim (γ ⊗expr e) (γ ⊗expr s)
_⊗expr_ {d = compu} γ (t ∷ T)     = (γ ⊗expr t) ∷ (γ ⊗expr T)

_⊗sub_ {p = p} {γ = γ} δ' ε
  = ⟨sub {T = Expr (δ' ⊗ p) compu} _⟨exp_ (idexpr {δ'}) (δ' ◃ γ)
δ' ⊗sub (σ -, x) = (δ' ⊗sub σ) -, (δ' ⊗expr x)

_⟨esub_ : Thinnable (γ ⇒[ Expr p d ]_)
_⟨esub_ = ⟨sub _⟨exp_ 


map : (f : ∀{δ} → svar p δ → svar q δ) → Expr p d γ' → Expr q d γ'
map {d = const} f (` x) = ` x
map {d = const} f (s ∙ t) = map f s ∙ map f t
map {d = const} f (bind t) = bind (map f t)
map {d = const} f (thunk x) = thunk (map f x)
map {p = p} {q = q} {d = const} f (ξ / σ) = f ξ / mapself σ
  where
    -- inline to shut up termination checker
    mapself : ∀ {n} → BwdVec (Com p γ') n → BwdVec (Com q γ') n
    mapself ε = ε
    mapself (xs -, x) = mapself xs -, map f x
map {d = compu} f (var x) = var x
map {d = compu} f (elim e x) = elim (map f e) (map f x)
map {d = compu} f (t ∷ T) = map f t ∷ map f T
\end{code}
}

We are able to generate a term from an expression and some opening
of an environment for the trusted pattern. Most of the cases recurse
structurally, while variables are simply opened to encompassing scope,
however we can note here how it is that we process our svar instantiations

\begin{code}
toTerm  : (γ ⊗ p) -Env → Expr p d γ' → Term d (γ + γ')
toTerm {γ = γ} {d = const} {γ' = γ'} penv (ξ / σ)
  = let σ'     = map-toTerm σ penv  in
    let id-fv  = id ⟨σ (γ ◃ γ')     in
      (ξ ‼ penv) /term ((id-fv ++ σ'))
\end{code}
That is to say, we first resolve the substitution of expressions to one of
terms (here we must inline a specialisation of map in order to satisfy Agda's
termination checker) before extending it with the identity substitution for
all the free variables and finally performing the substitution on the term
taken from the environment. We substitute the bound variables in the term
but ensure not to affect any free variables.
\hide{
\begin{code}
    where
      map-toTerm : ∀ {γ} → δ' ⇒[ Expr p d ] γ' → ((γ ⊗ p) -Env)  → δ' ⇒[ Term d ] (γ + γ')
      map-toTerm ε env = ε
      map-toTerm (σ -, x) env = map-toTerm σ env -, toTerm env x
toTerm {d = const} penv (` x)      = ` x
toTerm {d = const} penv (s ∙ t)    = (toTerm penv s) ∙ (toTerm penv t)
toTerm {d = const} penv (bind t)   = bind  (toTerm penv t) 
toTerm {d = const} penv (thunk x)  = ↠ (toTerm penv x)
toTerm {γ = γ} {d = compu} {γ' = γ'} penv (var x)
                                   = var (γ ⊗var x)
toTerm {d = compu} penv (elim e s) = elim (toTerm penv e) (toTerm penv s)
toTerm {d = compu} penv (t ∷ T)    = toTerm penv t ∷ toTerm penv T
\end{code}
}
