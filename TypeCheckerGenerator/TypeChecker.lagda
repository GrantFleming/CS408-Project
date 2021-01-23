\section{Checking Types}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module TypeChecker where
\end{code}

\begin{code}
open import Pattern using (⊗-identityʳ)
{-# REWRITE ⊗-identityʳ #-} 

open import CoreLanguage
open import Failable
open import Data.Maybe using (just; nothing)
open import Context using (Context; _‼V_) renaming (_,_ to _-,_)
open import Data.List using (List; []; _∷_)
open import Rules
open Pattern using (Pattern; _-Env; _∙_; thing; `; bind; _‼_; _-penv_; _⊗_; termFrom)
open import Expression using (toTerm)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Data.Char using (_==_)
open import Data.Bool using (true; false)
open import Data.Product using (_×_; proj₁; proj₂)
open import Thinning using (_⟨term_)
open import Data.String using (_++_)
\end{code}

\begin{code}
private
  variable
    d : Dir
    γ : Scope
    δ : Scope
    p : Pattern δ
    q : Pattern δ
    p' : Pattern γ
    q' : Pattern δ


open TypeRule
open UnivRule
open ∋rule

check : Rules → Context γ → (type : Term const γ)  → (term : Term d γ) → Failable ⊤

∋-check : Context γ               →
          Rules                   →
          List ∋rule              →
          (subject : Const γ) →
          (input : Const γ)   →
          Failable ⊤

type-check : Context γ               →
             Rules                   →
             List TypeRule           →
             (subject : Const γ) →
             Failable ⊤

univ-check : Context γ              →
             Rules                  →
             List UnivRule          →
             (input : Const γ)  →
             Failable ⊤

_≡ᵗ_ : Term d γ → Term d γ → Failable ⊤

check-premise : Context γ   →
                Rules       →
                p -Env      →
                q -Env      →
                Prem p q γ p' q'  →
                Failable (p' -Env × q' -Env)
check-premise {q = q} Γ rules@(rs t u ∋ e) penv qenv (type ξ θ)
  = do
    _ ← type-check  Γ rules t ((ξ ‼ qenv) ⟨term θ)
    succeed (thing (ξ ‼ qenv) , (qenv -penv ξ))
check-premise Γ rules penv qenv (T ∋' ξ [ θ ])
  = do
    _ ← check rules Γ (toTerm {γ = 0} penv T) ((ξ ‼ qenv) ⟨term θ)
    succeed ((thing (ξ ‼ qenv)) , (qenv -penv ξ))
check-premise Γ rules penv qenv (x ≡' x')
  = do
    _ ← toTerm {γ = 0}  penv x ≡ᵗ toTerm {γ = 0} penv x'
    succeed (` , qenv)
check-premise Γ rules@(rs t u ∋ e) penv qenv (univ x)
  = do
    _ ← univ-check Γ rules u (toTerm {γ = 0} penv x)
    succeed (` , qenv)
check-premise {γ = γ} Γ rules penv qenv (x ⊢' prem)
  = do
    (p'env , q'env) ← check-premise (Γ -, toTerm {γ = 0} penv x) rules penv qenv prem
    succeed ((bind p'env) , q'env)

check-premise-chain : ∀ {p : Pattern γ} {q : Pattern γ} {p' : Pattern γ} →
                      Context γ → Rules → p -Env → q -Env → Prems p q p' → Failable (p' -Env)
check-premise-chain Γ rules penv qenv (ε x)       = succeed penv
check-premise-chain Γ rules penv qenv (prem ⇉ prems)
 = do
     (p'env , q₁env) ← check-premise Γ rules penv qenv prem
     p''env ← check-premise-chain Γ rules (penv ∙ p'env) q₁env prems
     succeed p''env

run-∋rule : Context γ → Rules → (rule : ∋rule) → ((γ ⊗ (input rule)) -Env) → ((γ ⊗ (subject rule)) -Env) → Failable ⊤
run-∋rule {γ} Γ rules@(rs t u ∋ e) rule ienv senv
  = do
     _ ← type-check Γ rules t (termFrom (input rule) ienv)
     _ ← check-premise-chain Γ rules ienv senv (⊗premises γ (proj₂ (premises rule)))
     succeed tt

run-erule : Context γ                       →
            Rules                           →
            (rule : ElimRule)               →
            (γ ⊗ ElimRule.targetPat rule)  -Env →
            (γ ⊗ ElimRule.eliminator rule) -Env →
            Failable (Term const γ)
run-erule {γ} Γ rules rule T-env s-env
  = do
      p'env ← check-premise-chain Γ rules T-env s-env (⊗premises γ (proj₂ (premises rule)))
      succeed (toTerm p'env (output rule))
    where
      open ElimRule

-- check the precondition that the thing must be a type!
run-univrule : Context γ → Rules → (rule : UnivRule) → ((γ ⊗ (input rule)) -Env) → Failable ⊤
run-univrule {γ = γ} Γ rules@(rs t u ∋ e) rule env
  = do
     _ ← type-check Γ rules t (termFrom (input rule) env)
     _ ← check-premise-chain Γ rules env ` (⊗premises γ (proj₂ (premises rule)))
     succeed tt

run-typerule : Context γ → Rules → (rule : TypeRule) → ((γ ⊗ (subject rule)) -Env) → Failable ⊤
run-typerule {γ} Γ rules rule env
  = do
      _ ← check-premise-chain Γ rules ` env (⊗premises γ (proj₂ (premises rule)))
      succeed tt


{-# TERMINATING #-}
univ-check Γ rules  []              input
  = fail ("univ-check: " ++ (print input) ++ " is not a universe")
univ-check Γ rules (urule ∷ urules) input
  with match-univrule urule input
... | nothing = univ-check Γ rules urules input
... | just x = run-univrule Γ rules urule x


type-check  Γ rules []      ms
  = fail ("type-check: " ++ (print ms) ++ " is not a type")
type-check Γ rules (trule ∷ trules) ms
  with match-typerule trule ms
... | nothing = type-check Γ rules trules ms
... | just env = run-typerule Γ rules trule env


∋-check Γ rules []               sub inp
  = fail ("failed ∋-check: " ++ (print inp) ++ " ∋ " ++ (print sub))
∋-check Γ rules (∋-rule ∷ ∋rules) sub inp
  with match-∋rule ∋-rule inp sub
... | nothing = ∋-check Γ rules ∋rules sub inp
... | just (subj-env , input-envs) = run-∋rule Γ rules ∋-rule subj-env input-envs

elim-synth : Context γ                       →
             Rules                           →
             List ElimRule                   →
             (synth-type : Term const γ) →
             (eliminator : Term const γ) →
             Failable (Term const γ)
elim-synth Γ rules []             T s
  = fail ("elim-synth: failed to match elimination rule for target = " ++ (print T) ++ " and eliminator = " ++ (print s))
elim-synth Γ rules (erule ∷ erules) T s with match-erule erule T s
... | nothing              = elim-synth Γ rules erules T s
... | just (T-env , s-env) = run-erule Γ rules erule T-env s-env

-- equality TODO - implement operational semantics and revisit this
-- At the moment, equality is just syntactic
eqfail : Failable ⊤
eqfail = fail "Equality failure."

_≡v_ : Var γ → Var γ → Failable ⊤
ze   ≡v ze    = succeed tt
su v ≡v su v' = v ≡v v'
_    ≡v _     = eqfail

_≡ᵗ_ {const} (` x)    (` x₁) with x == x₁
... | false = eqfail
... | true  = succeed tt
_≡ᵗ_ {const} (x ∙ x₁) (x₂ ∙ x₃) = do
                                   _ ← x  ≡ᵗ x₂
                                   _ ← x₁ ≡ᵗ x₃
                                   return tt
_≡ᵗ_ {const} (bind x) (bind x') = x ≡ᵗ x'
_≡ᵗ_ {const} (thunk x) (thunk x') = x ≡ᵗ x'

_≡ᵗ_ {compu} (var x) (var x')        = x ≡v x'
_≡ᵗ_ {compu} (elim e s) (elim e' s') = do
                                        _ ← e ≡ᵗ e'
                                        _ ← s ≡ᵗ s'
                                        return tt
_≡ᵗ_ {compu} (t ∷ T) (t' ∷ T') = do  -- maybe we can ignore the annotation here?
                                        _ ← t ≡ᵗ t'
                                        _ ← T ≡ᵗ T'
                                        return tt
_ ≡ᵗ _  = eqfail

infer : Rules → Context γ → Term compu γ → Failable (Term const γ)
infer rules@(rs t u ∋ ee) Γ (var x)    = do
                            -- check postcondition:
                             _ ← type-check Γ rules t (x ‼V Γ)
                             succeed (x ‼V Γ)
infer rules@(rs t u ∋ ee) Γ (elim e s) = do
                             T ← infer rules Γ e
                             S ← elim-synth Γ rules ee T s
                             -- check postcondition:
                             _ ← type-check Γ rules t S
                             succeed S
infer rules@(rs tr u ∋ e) Γ (t ∷ T)  = do
                   -- postcondition checks in ∋-check
                   _ ← ∋-check Γ rules ∋ t T
                   succeed T

check {_} {const} rules Γ T (thunk x)       = check rules Γ T x
check {_} {const} rules@(rs tr u ∋ e) Γ T t = ∋-check Γ rules ∋ t T
check {_} {compu} rules@(rs tr u ∋ e) Γ T t = do
                            S ← infer rules Γ t
                            _ ← type-check Γ rules tr S
                            S ≡ᵗ T
\end{code}
}
