\section{Representing Judgements and Rules}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Rules where
\end{code}
}

\begin{code}
open import CoreLanguage
open import Thinning using (_⊑_; ι; _++_)
open import Pattern using (Pattern; svar; bind; _∙; ∙_; place; ⋆; _∙_; `; ⊥; _-Env; match; _-_; _⊗_; _⊗svar_)
open import Expression using (Expr; _⊗expr_)
open import Data.Product using (_×_; _,_; proj₁; Σ-syntax)
open import Data.List using (List)
open import Data.Char
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Maybe using (Maybe; just; _>>=_)
open import Relation.Binary.PropositionalEquality using (cong; sym; _≡_; refl)
\end{code}

\begin{code}
private
  variable
    δ : Scope
    δ' : Scope
    γ : Scope
    p : Pattern 0
    pᵍ : Pattern γ
    p` : Pattern (suc γ)
    q` : Pattern 0
    q`` : Pattern δ
    q : Pattern 0
    q' : Pattern 0

data Prem (p : Pattern δ) (q : Pattern δ) (γ : Scope) : (p' : Pattern γ) → (q' : Pattern δ) → Set where
   type    : (ξ : svar q δ') → (θ : δ' ⊑ γ) → Prem p q γ (place θ) (q - ξ)
   _∋'_[_] : (T : Expr p const γ) → (ξ : svar q δ') → (θ : δ' ⊑ γ)  → Prem p q γ (place θ) (q - ξ)
   _≡'_    : Expr p const γ → Expr p const γ → Prem p q γ (` '⊤') q
   univ    : Expr p const γ → Prem p q γ (` '⊤') q
   _⊢'_    : Expr p const γ → Prem p q (suc γ) p` q`` → Prem p q γ (bind p`) q``

helper : ∀ {δ'} (δ : Scope) → (q : Pattern γ) → (ξ : svar q δ') → (δ ⊗ q) - (δ ⊗svar ξ) ≡ δ ⊗ (q - ξ)
helper δ (s ∙ t)  (ξ ∙)     = cong (λ x → Pattern._∙_ x (δ ⊗ t)) (helper δ s ξ) 
helper δ (s ∙ t) (∙ ξ)      = cong (Pattern._∙_ (δ ⊗ s)) (helper δ t ξ)
helper δ (bind q) (bind ξ)  = cong bind (helper δ q ξ)
helper δ (place x) ⋆        = refl

⊗premise : ∀ {p' : Pattern γ} → 
                 (δ : Scope) →
                 Prem p q γ p' q' →
                 Prem (δ ⊗ p) (δ ⊗ q) (δ + γ) (δ ⊗ p')  (δ ⊗ q')
⊗premise {q = q} δ (type ξ θ)     rewrite sym (helper δ q ξ) = type (δ ⊗svar ξ) (ι ++ θ)
⊗premise {q = q} δ (T ∋' ξ [ θ ]) rewrite sym (helper δ q ξ) = (δ ⊗expr T) ∋' δ ⊗svar ξ [ ι ++ θ ]
⊗premise δ (x ≡' x₁)      = (δ ⊗expr x) ≡' (δ ⊗expr x₁)
⊗premise δ (univ x)       = univ (δ ⊗expr x)
⊗premise δ (_⊢'_ {p` = p`} x prem) = (δ ⊗expr x) ⊢' ⊗premise δ prem

-- We have a concept of a placeless thing, which represents any
-- pattern that contains no places
data _Placeless {γ : Scope} : Pattern γ → Set where
  `    : (c : Char) → ` c Placeless
  ⊥    : ⊥ Placeless
  _∙_  : {l r : Pattern γ} → (l Placeless) → (r Placeless) → (l ∙ r) Placeless
  bind : {t : Pattern (suc γ)} → (t Placeless) → (bind t) Placeless

-- we can remove places from a pattern and replace them with ` '⊤'
_-places : Pattern γ → Pattern γ
` x      -places = ` x
(s ∙ t)  -places = (s -places) ∙ (t -places)
bind t   -places = bind (t -places)
place x  -places = ` '⊤'
⊥        -places = ⊥

-- hence we can make a placeless thing from any pattern 
_placeless : (p : Pattern γ) → (p -places) Placeless
` x placeless      = ` x
(s ∙ t) placeless  = (s placeless) ∙ (t placeless)
bind p placeless   = bind (p placeless)
place x placeless  = ` '⊤'
⊥ placeless        = ⊥

-- we can also 'open' placeless things trivially, just fixing up the type
_⊗pl_ : ∀ {p : Pattern γ} → p Placeless → (δ : Scope) → (δ ⊗ p) Placeless
` c     ⊗pl δ = ` c
⊥       ⊗pl δ = ⊥
(s ∙ t) ⊗pl δ = (s ⊗pl δ) ∙ (t ⊗pl δ)
bind t  ⊗pl δ = bind (t ⊗pl δ)

private
  variable
    p' : Pattern 0
    q₁ : Pattern 0
    p₂ : Pattern 0

-- and a chain of Premises
private
  variable
    q₁` : Pattern γ
    p₂` : Pattern γ

data Prems (p₀ : Pattern γ) (q₀ : Pattern γ) : (p₂ : Pattern γ) → Set where
  ε : (q₀ Placeless) → Prems p₀ q₀ p₀
  _⇉_ : Prem p₀ q₀ γ pᵍ q₁` →
        Prems (p₀ ∙ pᵍ) q₁` p₂` →
        Prems p₀ q₀ p₂`
infixr 20 _⇉_

⊗premises : (δ : Scope) → Prems p q p₂ → Prems (δ ⊗ p) (δ ⊗ q) (δ ⊗ p₂)
⊗premises δ (ε x)           = ε (x ⊗pl δ)
⊗premises δ (prem ⇉ prems)  = ⊗premise δ prem ⇉ ⊗premises δ prems

record TypeRule : Set where
  field
    subject  : Pattern 0
    premises : Σ[ p' ∈ Pattern 0 ] Prems (` '⊤') subject p'
open TypeRule

match-typerule : (rule : TypeRule) → Term const γ → Maybe ((γ ⊗ (subject rule)) -Env)
match-typerule rule term = match term (subject rule)

record UnivRule : Set where
  field
    input    : Pattern 0
    premises : Σ[ p' ∈ Pattern 0 ] Prems input (` '⊤') p'
open UnivRule

match-univrule : (rule : UnivRule) → Term const γ → Maybe ((γ ⊗ (input rule)) -Env)
match-univrule rule term = match term (input rule)

record ∋rule : Set where
  field
    subject  : Pattern 0
    input    : Pattern 0
    premises : Σ[ p' ∈ Pattern 0 ] Prems input subject p'
open ∋rule

match-∋rule : (rule : ∋rule) → Term const γ → Term const γ →
              (Maybe (((γ ⊗ (input rule)) -Env) × ((γ ⊗ (subject rule)) -Env)))
match-∋rule rule Tterm tterm
  = do
      inenv  ← match Tterm (input rule)
      subenv ← match tterm (subject rule)
      just (inenv , subenv)

record ElimRule : Set where
  field
    targetPat  : Pattern 0
    eliminator : Pattern 0
    premises   : Σ[ p' ∈ Pattern 0 ] Prems targetPat eliminator p'
    output     : Expr (proj₁ premises) const 0

match-erule : (rule : ElimRule) →
              (T : Term const γ) →
              (s : Term const γ) →
              Maybe (((γ ⊗ (ElimRule.targetPat rule)) -Env) × ((γ ⊗ (ElimRule.eliminator rule)) -Env))
match-erule rule T s = do
                         T-env ← match T (targetPat rule)
                         s-env ← match s (eliminator rule)
                         just (T-env , s-env)
                       where
                         open ElimRule

data Rules : Set where
  rs : List TypeRule → List UnivRule → List ∋rule → List ElimRule → Rules
\end{code}
