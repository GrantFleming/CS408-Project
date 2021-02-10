\section{Semantics}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Semantics where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Pattern using (Pattern; _∙_; _⊗_; _-Env; match)
open import Context using (Context) renaming (_,_ to _-,_)
open import Data.String using (_++_)
open import Expression using (toTerm; Con)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Failable using (Failable; succeed; fail)
open import Data.Nat using (_+_; _≟_)
open import Thinning using (_⟨term_)
open import Rules using (∋rule; typeOf; bind-count)
open import Pattern using (`; _∙_; bind; place; thing; svar; svar-builder;
                           X; ⇚; ⇛; ↳; build; bind-count-bl)
open import Relation.Nullary using (yes; no; ¬_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (sym; subst; _≡_; refl)
open ∋rule
\end{code}
}

\hide{
\begin{code}
private
  variable
    γ : Scope
    δ : Scope
    d : Dir
\end{code}
}

Given the way that we represent typing rules, our type for $β$-rules
should not look unfamiliar. We match a rule by matching patterns for the
target, target type and eliminator and construct the reduced term
and its type from an expression and the resulting environment we
computed in the matching process.

Since we are matching a rule by matching patterns, the target, type and
eliminator in question must be in weak head normal form \hl{verify} and
so care should be taken to compute these forms before attempting to match
a β-rule.
\begin{code}
record β-rule : Set where
  field
    target targetType eliminator : Pattern 0
    redTerm redType : Con (target ∙ targetType ∙ eliminator) 0

  open Data.Maybe using (_>>=_)

  Rule-Env : {γ : Scope} → Set
  Rule-Env {γ} = ((γ ⊗ target)      ∙ 
                  (γ ⊗ targetType)  ∙
                  (γ ⊗ eliminator)) -Env

  β-match : (targ type elim : Const γ) → Maybe Rule-Env
  β-match tar ty el = do
                        t-env  ← match tar target
                        ty-env ← match ty targetType
                        e-env  ← match el eliminator
                        just (t-env ∙ ty-env ∙ e-env)
                      

  β-reduce  :  Rule-Env {γ} → Compu γ
  β-reduce env
    = ↞↞ (toTerm env redTerm) (toTerm env redType)
open β-rule        
\end{code}
We then define a function that will attempt a reduction with regards
to a list of β-rules by trying to match and apply a rule.
\hide{
\begin{code}
open import Failable using (_>>=_)
\end{code}
}
\begin{code}
findRule : List β-rule →
           (tar type elim : Const γ)  →
           Failable ( Σ[ r ∈ β-rule ] Rule-Env r {γ} )
findRule [] t ty e = fail ("No matching β-rule found for " ++
                           print t ++ " : " ++ print ty ++
                           " eliminated by " ++ print e)
findRule (r ∷ rs) t ty e with β-match r t ty e
... | nothing   = findRule rs t ty e
... | just env  = succeed (r , env)

reduce : List β-rule              →
         (tar type elim : Const γ)  →
         Failable (Compu γ)
reduce rules ta ty el
  = do
      (rule , env) ← findRule rules ta ty el
      succeed (β-reduce rule env)
\end{code}
Finally, we implement normalization by evaluation. We first define an evaluation
function that works in terms of a generic means of reduction and type synthesis
then provide our implementation of \emph{reflect} which eta-expands sub-terms of
the term so that the head of the sub-term matches the constructor of its given
type. Normalisation is then the composition of these functions - reducing as far
as possible before building the correct head form at each type. \hl{expand?}
\hide{
\begin{code}
open import EtaRule
open η-Rule
{-# TERMINATING #-}
\end{code}
}
\begin{code}
_-_-_∥_∥ :  (reducer : ∀ {γ} → (tar type elim : Const γ) → Failable (Compu γ)) →
           (inferer : ∀ {γ} → Context γ → (term : Term compu γ) → Failable (Term const γ)) →
           Context γ →
           Term d γ →
           Const γ
rd - inf - Γ ∥ T ∥ = ⟦ T ⟧ Γ
  where
    ⟦_⟧ : Term d γ → Context γ → Const γ
    ⟦_⟧ {const} (` x) Γ       = ` x
    ⟦_⟧ {const} (s ∙ t) Γ     = ⟦ s ⟧ Γ ∙ ⟦ t ⟧ Γ
    ⟦_⟧ {const} (bind t) Γ    = bind (⟦ t ⟧ (Γ Context., ` "unknown") )
    ⟦_⟧ {const} (thunk x) Γ   = ⟦ x ⟧ Γ
    ⟦_⟧ {compu} (var x) Γ     = thunk (var x)
    ⟦_⟧ {compu} (elim t e) Γ with inf Γ t
    ... | fail    n = thunk (elim (↞↞ (⟦ t ⟧ Γ) (` "unknown")) (⟦ e ⟧ Γ))
    ... | succeed ty with rd (⟦ t ⟧ Γ) ty (⟦ e ⟧ Γ)
    ... | succeed x = ⟦ x ⟧ Γ
    ... | fail x    = thunk (elim (↞↞ (⟦ t ⟧ Γ) ty) (⟦ e ⟧ Γ))
    ⟦_⟧ {compu} (t ∷ T) Γ   = ⟦ t ⟧ Γ
\end{code}
\hide{
\begin{code}
{-# TERMINATING #-}
\end{code}
}
\begin{code}
qt : List η-Rule → (ty tm : Const γ) → Const γ
qt {γ = γ} rs ty v with EtaRule.findRule rs ty
... | fail x    = v
... | succeed (r , i) = helper (i ∙ (eliminations r ty v)) X (eliminations r ty v)
  where
    helper : ∀ {γ'}{q : Pattern γ'} →
             ((γ ⊗ input (checkRule r)) ∙ (γ ⊗ (subject (checkRule r))))-Env →         
             (v : svar-builder (γ ⊗ (subject (checkRule r))) q) → 
             q -Env →
             Const ((bind-count-bl v) + γ)
    helper {γ' = γ'}{q = q} (i ∙ s) v elims with q | elims
    ... | ` x     | ` = ` x
    ... | ps ∙ pt | es ∙ et
      = helper (i ∙ s) (⇚ v) es ∙ helper (i ∙ s) (⇛ v) et
    ... | bind pt | bind et
      = bind (helper (i ∙ s) (↳ v) et)
    ... | place θ | thing el
      with bind-count (build v) + γ ≟ γ'
    ... | no ¬p = ` "Fuck it! It's impossible."
    ... | yes p = qt rs
          (typeOf (checkRule r) (build v) i s)
          (subst (λ x → Const x) (sym p) ((el ⟨term θ)))

normalize : List η-Rule →
             List β-rule → 
             (inferer : ∀ {γ} → Context γ → (term : Term compu γ) → Failable (Term const γ)) →
             Context γ →
             (type : Const γ)   →
             (term : Term d γ)  →
             Const γ
normalize ηs βs inf Γ ty = (qt ηs ty) ∘ (reduce βs - inf - Γ ∥_∥)
\end{code}
