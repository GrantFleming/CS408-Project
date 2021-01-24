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
open import Data.Char using (Char)
open import Data.Nat using (zero; suc; _+_)
open import BwdVec
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
    γ' : Scope
    d : Dir
    d' : Dir
\end{code}
}

Expressions allow us to define a way that we might construct a term from a
pattern. In the context of a conclusion of a typing rule, where a pattern
might match and sculpt out component parts of an input or subject,
expressions allow us to define an output in terms in terms of these component
parts. In a premise, it allows us to build an input in terms of the
conclusion and the output of all previous premise.

It mirrors the structure of our terms except that it includes the option
to instantiate a place in a pattern with some substitution of term variables
that it may depend on. When we are using an expression after matching against
the appropriate pattern and gaining an environment for it, this gives us the
necessary information to build a term.

\begin{code}
Expr : Pattern δ → Dir → Scoped

data con (p : Pattern δ) (γ : Scope) : Set
data com (p : Pattern δ) (γ : Scope) : Set

data con p γ where
  `      : Char → con p γ
  _∙_    : con p γ → con p γ → con p γ
  bind   : con p (suc γ) → con p γ
  thunk  : com p γ → con p γ
  _/_    : svar p γ' → γ' ⇒[ Expr p compu ] γ → con p γ
  
data com p γ where
  var    : Var γ → com p γ
  elim   : com p γ → con p γ → com p γ
  _∷_    : con p γ → con p γ → com p γ


Expr p const γ = con p γ
Expr p compu γ = com p γ
\end{code}

As is expected by now, we define various functions allowing us to thin,
weaken and open expressions and substitutions thereof for later use.

\begin{code}
_⟨exp_   : Thinnable (Expr p d)
_^exp    : Weakenable (Expr p d)
_^/exp   : Weakenable (γ ⇒[ Expr p d ]_)
_⊗expr_  : (γ : Scope) → Expr p d δ → Expr (γ ⊗ p) d (γ + δ)
\end{code}

\hide{
\begin{code}
infixr 20 _∙_

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


_^exp {p = p} {d = d} = weaken {T = Expr p d} _⟨exp_

_^/exp {p = p} {d = d}  = ^sub {T = Expr p d}  _⟨exp_

idexpr : γ ⇒[ Expr p compu ] γ
idexpr {zero}          = ε
idexpr {suc γ} {p = p}
  = ^sub {T = Expr p compu} _⟨exp_ idexpr -, var (fromNum γ)

_⊗sub_ : (δ' : Scope) →
         δ ⇒[ Expr p compu ] γ →
         (δ' + δ) ⇒[ Expr (δ' ⊗  p) compu ] (δ' + γ)
_⊗sub_ {p = p} {γ = γ} δ' ε
  = ⟨sub {T = Expr (δ' ⊗ p) compu} _⟨exp_ (idexpr {δ'}) (δ' ◃ γ)
δ' ⊗sub (σ -, x) = (δ' ⊗sub σ) -, (δ' ⊗expr x)

_⊗expr_ {d = const} γ (` x)       = ` x
_⊗expr_ {d = const} γ (s ∙ t)     = (γ ⊗expr s) ∙ (γ ⊗expr t)
_⊗expr_ {d = const} γ (bind x)    = bind (γ ⊗expr x)
_⊗expr_ {d = const} γ (thunk x)   = thunk (γ ⊗expr x)
_⊗expr_ {d = const} γ (ξ / σ)     = (γ ⊗svar ξ) / (γ ⊗sub σ)
_⊗expr_ {d = compu} γ (var x)     = var (γ ⊗var x)
_⊗expr_ {d = compu} γ (elim e s)  = elim (γ ⊗expr e) (γ ⊗expr s)
_⊗expr_ {d = compu} γ (t ∷ T)     = (γ ⊗expr t) ∷ (γ ⊗expr T)
\end{code}
}

Finally we are able to generate a term from an expression and some opening
of the appropriate environment. Most of the cases recurse structurally, while
variables are simply opened to encompassing scope, however we can note here
how it is that we process our svar instantiations

\begin{code}
toTerm  : (γ ⊗ p) -Env → Expr p d γ' → Term d (γ + γ')
-- ...
toTerm {γ = γ} {d = const} {γ' = γ'} penv (ξ / σ)
  = let σ'     = map-toTerm σ penv  in
    let id-fv  = id ⟨σ (γ ◃ γ')     in
      (ξ ‼ penv) /term ((id-fv ++ σ'))
-- ...
\end{code}

That is to say, we first resolve the substitution of expressions to one of
terms (here we must inline a specialisation of map in order to satisfy Agda's
termination checker) before extending it with the identity substitution for
all the free variables and finally performing the substitution on the term
taken from the environment.

In short, we substitute the bound variables in the term but ensure not to
affect any free variables that may exist.

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
