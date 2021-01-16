\section{Representing Judgements and Rules}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Rules where
\end{code}
}

\begin{code}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat.Properties using (+-suc; +-identityʳ)
{-# REWRITE +-identityʳ #-} -- to avoid the tedium

open import CoreLanguage
open import Thinning using (_⊑_; Scoped; Ø; ι; ε; _⇒[_]_; _O; _I; Thinnable; _◃_; _++_) renaming (_∘_ to _∘∘_)
import Pattern as Pat
open Pat using (Pattern; svar; bind; _∙; ∙_; place; ⋆; _∙_; `; ⊥; _⟨svar_; _-Env; match; _-_; _⟨pat_; _⊗_; _⊗svar_)
open Pat.Expression using (Expression; Expr; econ; lcon; ecom; lcom; _/_; ess; `; _⟨exp_; _⊗expr_) renaming (_∙_ to _∘_)
open import Data.Product using (_×_; _,_; proj₁; Σ-syntax)
open import Data.List using (List)
open import Data.Char
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Maybe using (Maybe; just; nothing; map; _>>=_)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
\end{code}

\begin{code}
-- we need the concept of a Premise that obtains a certain amount of trust

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
    p'' : Pattern δ

data Prem (p : Pattern 0) (q : Pattern 0) (γ : Scope) : (p' : Pattern γ) → (q' : Pattern 0) → Set where
   type : (ξ : svar q δ) → (θ : δ ⊑ γ) → Prem p q γ (place θ) (q - ξ)
   _∋'_[_] : (T : Expr p lib const γ) → (ξ : svar q δ) → (θ : δ ⊑ γ)  → Prem p q γ (place θ) (q - ξ)
   _≡'_ : Expr p lib const γ → Expr p lib const γ → Prem p q γ (` '⊤') q
   univ : Expr p lib const γ → Prem p q γ (` '⊤') q
   _⊢'_ : Expr p lib const γ → Prem p q (suc γ) p` q` → Prem p q γ (bind p`) q`


data ActualPrem (p : Pattern δ) (q : Pattern δ) (γ : Scope) : (p' : Pattern γ) → (q' : Pattern δ) → Set where
   type    : (ξ : svar q δ') → (θ : δ' ⊑ γ) → ActualPrem p q γ (place θ) (q - ξ)
   _∋'_[_] : (T : Expr p lib const γ) → (ξ : svar q δ') → (θ : δ' ⊑ γ)  → ActualPrem p q γ (place θ) (q - ξ)
   _≡'_    : Expr p lib const γ → Expr p lib const γ → ActualPrem p q γ (` '⊤') q
   univ    : Expr p lib const γ → ActualPrem p q γ (` '⊤') q
   _⊢'_    : Expr p lib const γ → ActualPrem p q (suc γ) p` q`` → ActualPrem p q γ (bind p`) q``



helper : ∀ {δ'} (δ : Scope) → (q : Pattern γ) → (ξ : svar q δ') → (δ ⊗ q) - (ξ ⊗svar δ) ≡ δ ⊗ (q - ξ)
helper δ (s ∙ t)  (ξ ∙)     = cong (λ x → Pattern._∙_ x (δ ⊗ t)) (helper δ s ξ) 
helper δ (s ∙ t) (∙ ξ)      = cong (Pattern._∙_ (δ ⊗ s)) (helper δ t ξ)
helper δ (bind q) (bind ξ)  = cong bind (helper δ q ξ)
helper δ (place x) ⋆        = refl

actual-premise : ∀ {p' : Pattern γ} → 
                 (δ : Scope) →
                 Prem p q γ p' q' →
                 ActualPrem (δ ⊗ p) (δ ⊗ q) (δ + γ) (δ ⊗ p')  (δ ⊗ q')
actual-premise {q = q} δ (type ξ θ)     rewrite sym (helper δ q ξ) = type (ξ ⊗svar δ) (ι ++ θ)
actual-premise {q = q} δ (T ∋' ξ [ θ ]) rewrite sym (helper δ q ξ) = (T ⊗expr δ) ∋' ξ ⊗svar δ [ ι ++ θ ]
actual-premise δ (x ≡' x₁)      = (x ⊗expr δ) ≡' (x₁ ⊗expr δ)
actual-premise δ (univ x)       = univ (x ⊗expr δ)
actual-premise δ (_⊢'_ {p` = p`} x prem) = (x ⊗expr δ) ⊢' actual-premise δ prem

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

-- we can thin premises
_⟨prem_ : Prem p q δ p'' q' → (θ : δ ⊑ γ)  → Prem p q γ (p'' ⟨pat θ) q'
type ξ θ₁       ⟨prem θ = type ξ (θ₁ ∘∘ θ)
(T ∋' ξ [ θ₁ ]) ⟨prem θ = (T ⟨exp θ) ∋' ξ [ θ₁ ∘∘ θ ]
(x ≡' x₁)       ⟨prem θ = (x ⟨exp θ) ≡' (x₁ ⟨exp θ)
univ x          ⟨prem θ = univ (x ⟨exp θ)
(x ⊢' prem)     ⟨prem θ = (x ⟨exp θ) ⊢' (prem ⟨prem (θ I))

private
  variable
    p' : Pattern 0
    q₁ : Pattern 0
    p₂ : Pattern 0
    n : ℕ

-- and a chain of Premises

data Prems (p₀ : Pattern 0) (q₀ : Pattern 0) : (p₂ : Pattern 0) → Set where
  ε : (q₀ Placeless) → Prems p₀ q₀ p₀
  _⇉_ : Prem p₀ q₀ 0 p' q₁ →
        Prems (p₀ ∙ p') q₁ p₂ →
        Prems p₀ q₀ p₂
infixr 20 _⇉_

private
  variable
    pᵈ : Pattern δ
    q₁` : Pattern γ
    p₂` : Pattern γ

data ActualPrems (p₀ : Pattern γ) (q₀ : Pattern γ) : (p₂ : Pattern γ) → Set where
  ε : (q₀ Placeless) → ActualPrems p₀ q₀ p₀
  _⇉_ : ActualPrem p₀ q₀ γ pᵍ q₁` →
        ActualPrems (p₀ ∙ pᵍ) q₁` p₂` →
        ActualPrems p₀ q₀ p₂`

actual-premises : (δ : Scope) → Prems p q p₂ → ActualPrems (δ ⊗ p) (δ ⊗ q) (δ ⊗ p₂)
actual-premises δ (ε x)           = ε (x ⊗pl δ)
actual-premises δ (prem ⇉ prems)  = actual-premise δ prem ⇉ actual-premises δ prems

record TypeRule : Set where
  field
    subject  : Pattern 0
    premises : Σ[ p' ∈ Pattern 0 ] Prems (` '⊤') subject p'
open TypeRule

match-typerule : (rule : TypeRule) → Term lib const γ → Maybe ((γ ⊗ (subject rule)) -Env)
match-typerule rule term = match term (subject rule)

record UnivRule : Set where
  field
    input    : Pattern 0
    premises : Σ[ p' ∈ Pattern 0 ] Prems input (` '⊤') p'
open UnivRule

match-univrule : (rule : UnivRule) → Term lib const γ → Maybe ((γ ⊗ (input rule)) -Env)
match-univrule rule term = match term (input rule)

record ∋rule : Set where
  field
    subject  : Pattern 0
    input    : Pattern 0
    premises : Σ[ p' ∈ Pattern 0 ] Prems input subject p'
open ∋rule

open import Data.Unit using (⊤; tt)

match-∋rule : (rule : ∋rule) → Term lib const γ → Term lib const γ →
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
    output     : Expr (proj₁ premises) lib const 0

match-erule : (rule : ElimRule) →
              (T : Term lib const γ) →
              (s : Term lib const γ) →
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
