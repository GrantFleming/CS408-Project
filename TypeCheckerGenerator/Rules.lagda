\section{Representing Judgements and Rules}

\hide{
\begin{code}
module Rules where
\end{code}
}

\begin{code}
open import CoreLanguage
open import Thinning using (_⊑_; Scoped; Ø; ι; ε; _⇒[_]_; _O)
import Pattern as Pat
open Pat using (Pattern; svar; bind; _∙; ∙_; place; ⋆; _∙_; `; ⊥; s-scope; _⟨svar_; _-Env; match; _-_)
open Pat.Expression using (Expression; Expr; econ; lcon; ecom; lcom; _/_; ess; `) renaming (_∙_ to _∘_)
open import Data.Product using (_×_; _,_; proj₁; Σ-syntax)
open import Data.List using (List)
open import Data.Char
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing; map; _>>=_)
\end{code}

\begin{code}
-- we need the concept of a Premise that obtains a certain amount of trust

private
  variable
    δ : Scope
    γ : Scope
    p : Pattern 0
    p` : Pattern (suc γ)
    q` : Pattern 0

data Prem (s : s-scope) (q : Pattern 0) (γ : Scope) : (p' : Pattern γ) → (q' : Pattern 0) → Set where
   type : (ξ : svar q δ) → (θ : δ ⊑ γ) → Prem s q γ (place θ) (q - ξ)
   _∋'_[_] : (T : Expr s lib const γ) → (ξ : svar q (proj₁ s)) → (θ : (proj₁ s) ⊑ γ) → Prem s q γ (place θ) (q - ξ)
   _≡'_ : Expr s lib const γ → Expr s lib const γ → Prem s q γ (` '⊤') q
   univ : Expr s lib const γ → Prem s q γ (` '⊤') q
   _⊢'_ : Expr s lib const γ → Prem s q (suc γ) p` q` → Prem s q γ (bind p`) q`
  
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

private
  variable
    p' : Pattern 0
    q₁ : Pattern 0
    p₂ : Pattern 0
    n : ℕ

-- and a chain of Premises

data Prems (δ : Scope) (p₀ : Pattern 0) (q₀ : Pattern 0) : (p₂ : Pattern 0) → Set where
  ε : (q₀ Placeless) → Prems δ p₀ q₀ p₀
  _⇉_ : Prem (δ , p₀) q₀ 0 p' q₁ →
        Prems δ (p₀ ∙ p') q₁ p₂ →
        Prems δ p₀ q₀ p₂
infixr 20 _⇉_

record TypeRule : Set where
  field
    subject  : Pattern 0
    premises : Σ[ p' ∈ Pattern 0 ] Prems 0 (` '⊤') subject p'
open TypeRule

match-typerule : (rule : TypeRule) → Term lib const γ → Maybe ((subject rule) -Env)
match-typerule rule term = match term (subject rule)

record UnivRule : Set where
  field
    input    : Pattern 0
    premises : Σ[ p' ∈ Pattern 0 ] Prems 0 input (` '⊤') p'
open UnivRule

match-univrule : (rule : UnivRule) → Term lib const γ → Maybe ((input rule) -Env)
match-univrule rule term = match term (input rule)

record ∋rule : Set where
  field
    subject  : Pattern 0
    input    : Pattern 0
    premises : Σ[ p' ∈ Pattern 0 ] Prems 0 input subject p'
open ∋rule

match-∋rule : (rule : ∋rule) → Term lib const γ → Term lib const γ →
              (Maybe (((input rule) -Env) × ((subject rule) -Env)))
match-∋rule rule Tterm tterm
  = do
      inenv  ← match Tterm (input rule)
      subenv ← match tterm (subject rule)
      just (inenv , subenv)
                        
record ElimRule : Set where
  field
    target     : Scope
    targetPat  : Pattern 0
    eliminator : Pattern 0
    premises   : Σ[ p' ∈ Pattern 0 ] Prems target targetPat eliminator p'
    output     : Expr (target , proj₁ premises) lib const 0

erule-envs : ElimRule → Set
erule-envs rule = Maybe (((targetPat rule) -Env) × ((eliminator rule) -Env)) where open ElimRule

match-erule : (rule : ElimRule) → (T : Term lib const γ) → (s : Term lib const γ) → erule-envs rule
match-erule rule T s = do
                         T-env ← match T (targetPat rule)
                         s-env ← match s (eliminator rule)
                         just (T-env , s-env)
                       where
                         open ElimRule

data Rules : Set where
  rs : List TypeRule → List UnivRule → List ∋rule → List ElimRule → Rules

\end{code}
