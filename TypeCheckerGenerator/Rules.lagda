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
open Pat using (Pattern; svar; bind; _∙; ∙_; place; ⋆; _∙_; `; ⊥; s-scope; _⟨svar_ )
open Pat.Expression using (Expression; Expr; econ; lcon; ecom; lcom; _/_; ess; `) renaming (_∙_ to _∘_)
open import Data.Product using (_,_; proj₂; proj₁)
open import Data.Char
open import Data.Nat using (suc)
open import Data.Maybe using (Maybe; just; nothing)
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
    
_-_ : (p : Pattern γ) → svar p δ → Pattern γ
(p ∙ q) - (ξ ∙)  = (p - ξ) ∙ q
(p ∙ q) - (∙ ξ)  = p ∙ (q - ξ)
bind p  - bind ξ = bind (p - ξ)
place x - ⋆      = ` '⊤' 

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

record Rule {p' : Pattern 0} (e : Scope) (p₀ : Pattern 0) : Set where
  field
    subject    : Maybe (Pattern 0)
    conclusion : Conclusion subject
    premises   : Prems e p₀ (strip subject) p'
open Rule

{-record ElimRule : Set where
  field
    target     : {!!}
    eliminator : {!!}
    premises   : {!!}-}

-- Types of certain rules (these are ones that users might need supply

TypeRule : (q : Pattern 0) → Prems 0 (` '⊤') q p' → Rule 0 (` '⊤')
subject    (TypeRule q prems) = just q
conclusion (TypeRule q prems) = TYPE q
premises   (TypeRule q prems) = prems

CheckRule : (T : Pattern 0) → (t : Pattern 0) → Prems 0 T t p' → Rule 0 T
subject    (CheckRule T t prems) = just t
conclusion (CheckRule T t prems) = T ∋ t
premises   (CheckRule T t prems) = prems

UnivRule : (p : Pattern 0) → Prems 0 p (` '⊤') p' → Rule 0 p
subject    (UnivRule p prems) = nothing
conclusion (UnivRule p prems) = UNIV p
premises   (UnivRule p prems) = prems

--ElRule : (e : Pattern 0) → Prems 0 {!!} {!!} {!!} → Rule 0 p
--ElRule e prems = {!!}

-- There are certain rules that exist regardless of the type theory:

-- There are two globally presented rules (rules which explicitly talk about the context)
-- There are context extension and type lookup

-- you can synthesize the type of a variable

-- TO DO

-- you can synthesize the type of anything with a type annotation

-- you can embed synthesizable things in checkable things

-- TO DO

-- if n is in a Universe then it is a type

-- TO DO (afterwards clean up the STLC example unnecessary rules)

-- reflexivity

-- TO DO

-- These rules are stored together in some structure

-- TO DO


\end{code}
