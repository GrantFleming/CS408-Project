\section{A Notion of Context}

\hide{
\begin{code}
module Context (T : Set) where

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Properties using (suc-injective; +-identityʳ; +-suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; refl; trans; cong; sym)
\end{code}
}


We begin by outlining the internal representation of contexts that will be used
heavily thoughout. Although a simple list captures the required functionality of
an ordered collection, we choose a more careful representation so that life is
a little easier down the line.

In preparation for constraint solving and polymorphism in future, we design our
contexts to make this process easier. Taking inspiration from Gundry, McBride
and McKinna \cite{TypeInferenceInContext} we use our context to explicitly track
type variables, and allow the contexts to container a marker for delimiting
Hindley-Milner style generalization later. We construct this entire module
generalizing over a representation of types (T).

We firstly outline a context entry, allowing it to be attached to no declaration
so that we might introduce fresh variables that are not yet constrained to be
any type in particular. We make a decision to use the same system for type and
term variables.

\hide{
\begin{code}
private
  variable
    n : ℕ
\end{code}
}

\begin{code}
VarName = ℕ

data Decl : Set where
  ‼  : T → Decl
  ⁇  : Decl

data Entry : Set where
  _∷=_ : VarName → Decl → Entry

\end{code}

We then define our contexts as families indexed by the number of entries, this allows
for easy scope checking. In order to do this we include two distinct 'extension'
constructors so that adding a generalisation delimiter does not increase the size
of the context. Convenience functions are also provided for context extension and
lookup.

\begin{code}
data Context : ℕ → Set where
  ε        : Context 0
  _-,_     : Context n → Entry → Context (suc n)
  _∘       : Context n → Context n
  skipvar  : Context n → Context (suc n)

private
  variable
    Γ : Context n
    m : ℕ
    Θ : Context m
    e : Entry
    d : Decl
    t : T
    v : VarName
    v' : VarName

extend : Context n → T → Context (suc n)
extend {n} c t  = c -, (n ∷= ‼ t)

comp : (n : ℕ) → (m : ℕ) → (n ≡ m) ⊎ (n ≢ m)
comp zero zero = inj₁ refl
comp zero (suc m) = inj₂ λ ()
comp (suc n) zero = inj₂ λ ()
comp (suc n) (suc m) with comp n m
... | inj₁ eq   =  inj₁ (cong suc eq)
... | inj₂ neq  =  inj₂ (λ x → neq (suc-injective x))

self-comp : ∀ {n} → comp n n ≡ inj₁ refl
self-comp {zero}   = refl
self-comp {suc n} with comp n n
... | inj₁ refl  = refl
... | inj₂ ¬n≡n  = ⊥-elim (¬n≡n refl)

lookup : Context n → VarName → Maybe Decl
lookup  ε               v  = nothing
lookup (c ∘ )           v  = lookup c v
lookup (skipvar c)      v  = lookup c v
lookup (c -, (x ∷= d))  v  with comp v x
... | inj₁ eq   = just d
... | inj₂ neq  = lookup c v

clear-delim : Context n → Context n
clear-delim (Γ ∘)       = clear-delim Γ
clear-delim ε           = ε
clear-delim (Γ -, e)    = (clear-delim Γ) -, e
clear-delim (skipvar x) = skipvar (clear-delim x)

_-_ : Context n → VarName → Context n
ε               - v  = ε
(Γ ∘)           - v  = (Γ - v) ∘
(skipvar c)     - v  = skipvar (c - v)
(Γ -, (x ∷= d)) - v with comp x v
... | inj₁ eq   = skipvar Γ
... | inj₂ neq  = (Γ - v) -, (x ∷= d)

irr-add : ∀ {n} {x} {d} {v'} → (c : Context n)  → v' ≢ x → lookup (c -, (x ∷= d)) v' ≡ lookup c v'
irr-add {x = x} {v' = v'} c neq with comp v' x
... | inj₁ refl = ⊥-elim (neq refl)
... | inj₂ _ = refl

irr-removal : ∀ {n} {v v' : ℕ} → (c : Context n)  → v ≢ v' → lookup (c - v) v' ≡ lookup c v'
irr-removal ε neq = refl
irr-removal {v = v} {v' = v'} (c -, (x ∷= d)) neq with comp v' v
... | inj₁ refl = ⊥-elim (neq refl)
... | inj₂ y with comp x v | comp v' x
... | inj₁ refl | inj₁ refl = ⊥-elim (neq refl)
... | inj₁ refl | inj₂ y₁ = refl
... | inj₂ y₁ | inj₁ refl rewrite self-comp {v'} = refl
... | inj₂ y₁ | inj₂ y₂ = trans (irr-add (c - v) y₂) (irr-removal c neq)
irr-removal (c ∘) neq = irr-removal c neq
irr-removal (skipvar c) neq = irr-removal c neq

lemma : ∀ {v} {v'} → v ≢ v' →
        lookup Γ v' ≡ just (‼ t) →
        lookup (Γ - v) v' ≡ just (‼ t)
        
lemma {Γ = c -, (x ∷= d)} {v = v} {v' = v'} v≢v' inΓ with comp x v | comp v' x
... | inj₁ refl | inj₁ refl    = ⊥-elim (v≢v' refl)
... | inj₁ refl | inj₂ neq     = inΓ
... | inj₂ neq  | inj₁ refl rewrite self-comp {x} = inΓ
... | inj₂ neq  | inj₂ neq' = trans (irr-add (c - v) neq') (lemma {Γ = c} v≢v' inΓ)

lemma {Γ = c ∘}       v≢v' inΓ = trans (irr-removal c v≢v') inΓ
lemma {Γ = skipvar Γ} v≢v' inΓ rewrite sym inΓ = irr-removal Γ v≢v'

offset : (m : ℕ) → Context n → Context (m + n)
offset zero c                   = c
offset (suc m)  ε               = skipvar (offset m ε)
offset {suc n} (suc m) (c -, (v ∷= d)) rewrite +-suc m n = (offset (suc m) c) -, ((suc m + v) ∷= d)
offset (suc m) (c ∘)            = offset (suc m) c ∘
offset {suc n} (suc m) (skipvar c) rewrite +-suc m n = skipvar (offset (suc m) c)

-- BE CAREFUL WITH THIS! IT MIGHT NOT DO WHAT YOU THINK!
-- SHOULD OLD BE USED WHEN SECOND ARGUMENT IS OFFSET
-- WILL CLEAR ALL DELIMITERS IN EITHER CONTEXT
private
  merge : ∀ {n} {m} → Context n → Context (n + m) → Context (n + m)
  merge {n} {zero}  old new rewrite +-identityʳ n   = clear-delim old 
  merge {zero}  {suc m}  old          (new -, e)    = (merge old new) -, e
  merge {zero}  {suc m}  old          (new ∘)       = merge old new
  merge {zero}  {suc m}  old          (skipvar new) = skipvar (merge old new)
  merge {suc n} {suc m} (old -, e)    (new -, e')   rewrite +-suc n m
                                                    = (merge (old -, e) new) -, e'
  merge {suc n} {suc m} (old ∘)       (new -, e)    = merge old (new -, e)
  merge {suc n} {suc m} (skipvar old) (new -, e)    = (merge old new) -, e
  merge {suc n} {suc m}  old          (new ∘)       = merge old new
  merge {suc n} {suc m}  old          (skipvar new) rewrite +-suc n m
                                                  = skipvar (merge old new)

_⊕_ : Context n → Context m → Context (n + m)
_⊕_  {n} Γ Θ = merge Γ (offset n Θ)

\end{code}


\subsection{Well scoped variables}

Now we reconcile our notion of contexts with that of type and scope safe
syntax outlined by G. Allais et al. \cite{DBLP:journals/corr/abs-2001-11001},
ensuring that both types of variables we provide are type and scope safe.
We choose to implement variables as both named variables and de-bruijn
indices here so that we may use the benefits of either method when required later
as described by McBride and McKinna \cite{DBLP:conf/haskell/McBrideM04}.

\begin{code}
data FVar (t : T) (c : Context n) : Set where
  var  : (v : VarName) → lookup c v ≡ just (‼ t) → FVar t c
\end{code}


