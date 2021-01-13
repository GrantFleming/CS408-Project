\section{Representing Judgements and Rules}

\hide{
\begin{code}
module Rules where
\end{code}
}

\begin{code}
open import CoreLanguage
open import Judgement
open import Thinning using (_⊑_; Scoped; Ø; ι; ε; _⇒[_]_; _O)
import Pattern as Pat
open Pat using (Pattern; svar; bind; _∙; ∙_; place; ⋆; _∙_; `; ⊥; s-scope; _⟨svar_; _-Env; match; match-all; _-_)
open Pat.Expression using (Expression; Expr; econ; lcon; ecom; lcom; _/_; ess; `) renaming (_∙_ to _∘_)
open import Data.Product using (_×_; _,_; proj₂; proj₁; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Char
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing; map; _>>=_)
open import Data.Empty renaming (⊥ to bot)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Judgement using (Judgement; J-Type; TY; NI; UNI; _≡ᵇ_)
open Judgement.Judgement
open import Data.Bool using (true; false)
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

strip : Maybe (Pattern γ) → (Pattern γ)
strip nothing  = ` '⊤'
strip (just x) = x

Conclusion : Maybe (Pattern 0) → Set
Conclusion p = Judgement Pattern Pattern Expression 0 p

private
  variable
    p₀ : Pattern 0

record ConstRule : Set where
  field
    subject    : Maybe (Pattern 0)
    conclusion : Conclusion subject
    trusted    : Pattern 0
    premises   : Σ[ p' ∈ Pattern 0 ] Prems 0 trusted (strip subject) p'
open ConstRule

private
  variable
    X : Set

menv : ConstRule → Set
menv rule with subject rule
... | nothing = ⊤
... | just x  = x -Env

out : ConstRule → Set
out rule = Maybe ((menv rule) × All _-Env (input (conclusion rule)))

--match t p
-- matching a ConstRule should match the subject and the inputs
-- TO DO clean this up
match-crule : (rule : ConstRule) → J-Type  →(subject : Maybe (Term lib const δ)) → (inputs : Vec (Term lib const δ) n) → out rule
match-crule record { subject = nothing } _ (just x) _ = nothing
match-crule record { subject = just x } _ nothing _ = nothing
match-crule record { subject = nothing;
                    conclusion = record {input = inputs; j-type = j'}}
           j nothing ins with j ≡ᵇ j'
... | false = nothing
... | true  = do
                ins ← match-all ins inputs
                just (tt , ins)
match-crule record { subject = (just p) ;
                    conclusion = record { input = inputs; j-type = j' }}
           j (just x) ins with j ≡ᵇ j'
... | false = nothing
... | true  = do
                s ← match x p
                ins ← match-all ins inputs
                just (s , ins)

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

-- Types of certain rules (these are ones that users might need supply

TypeRule : (q : Pattern 0) → (p' : Pattern 0) → Prems 0 (` '⊤') q p' → ConstRule
subject    (TypeRule q  p' prems) = just q
conclusion (TypeRule q  p' prems) = TYPE q
trusted    (TypeRule q  p' prems) = ` '⊤'
premises   (TypeRule q  p' prems) = p' , prems

CheckRule : (T : Pattern 0) → (t : Pattern 0) → (p' : Pattern 0) → Prems 0 T t p' → ConstRule
subject    (CheckRule T t p' prems) = just t
conclusion (CheckRule T t p' prems) = T ∋ t
trusted    (CheckRule T t p' prems) = T
premises   (CheckRule T t p' prems) = p' , prems

UnivRule : (u : Pattern 0) → (p' : Pattern 0) → Prems 0 u (` '⊤') p' → ConstRule
subject    (UnivRule u p' prems) = nothing
conclusion (UnivRule u p' prems) = UNIV u
trusted    (UnivRule u p' prems) = u
premises   (UnivRule u p' prems) = p' , prems
\end{code}
