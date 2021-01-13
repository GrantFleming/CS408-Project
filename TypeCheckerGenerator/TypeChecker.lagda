\section{Checking Types}

\begin{code}
module TypeChecker where
\end{code}

\begin{code}
open import CoreLanguage
open import Failable
open import Data.Maybe using (Maybe; just; nothing)
open import Context using (Context)
open import Data.List using (List; []; _∷_)
open import Rules
import Pattern as Pat
open Pat using (Pattern; _-Env; _∙_; thing; `; bind; s-scope; svar; _‼_; _-penv_; termFrom)
open Pat.Expression using (Expression; Expr; lcon; toTerm; e-Env; _^eenv)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Context using (Context; _‼V_) renaming (_,_ to _-,_)
open import Data.Char using (_==_)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; proj₁; proj₂)
open import Thinning using (_⟨term_; ε)
\end{code}

\begin{code}
private
  variable
    l : Lib
    d : Dir
    γ : Scope
    p : Pattern 0
    p' : Pattern γ    
    q : Pattern 0
    q' : Pattern 0
    n : ℕ
    δ : Scope
    s : s-scope

open TypeRule
open UnivRule
open ∋rule

∋-check : Rules                   →
          List ∋rule              →
          (subject : Lib-Const γ) →
          (input : Lib-Const γ)   →
          Failable ⊤

type-check : Rules                   →
             List TypeRule           →
             (subject : Lib-Const γ) →
             Failable ⊤

univ-check : Rules                  →
             List UnivRule          →
             (input : Lib-Const γ)  →
             Failable ⊤

_≡_ : Term l d γ → Term l d γ → Failable ⊤


check-premise : Rules             →
                (proj₂ s) -Env    →
                e-Env (proj₁ s) γ →
                q -Env            →
                Prem s q γ p' q'  →
                Failable (p' -Env × q' -Env)
check-premise rules@(rs t u ∋ e) penv γenv qenv (type ξ θ)
  = do
      _ ← type-check rules t ((ξ ‼ qenv) ⟨term θ)
      succeed ((thing (ξ ‼ qenv)) , (qenv -penv ξ))
check-premise rules@(rs t u ∋ e) penv γenv qenv (T ∋' ξ [ θ ])
  = do
    _ ← ∋-check rules ∋ ((ξ ‼ qenv) ⟨term θ) (toTerm penv γenv T)
    succeed ((thing (ξ ‼ qenv)) , (qenv -penv ξ))
check-premise rules penv γenv qenv (x ≡' x')
  = do
    _ ← toTerm penv γenv x ≡ toTerm penv γenv x'
    succeed (` , qenv)
check-premise rules@(rs t u ∋ e) penv γenv qenv (univ x)
  = do
      _ ← univ-check rules u (toTerm penv γenv x)
      succeed (` , qenv)
check-premise rules penv γenv qenv (x ⊢' p)
  = do
      (p'env , q'env) ← check-premise rules penv (γenv ^eenv) qenv p
      succeed (bind p'env , q'env)

check-premise-chain : Rules → p -Env → e-Env δ 0 → q -Env → Prems δ p q p' → Failable ⊤
check-premise-chain rules penv eenv qenv (ε x)    = succeed tt
check-premise-chain rules penv eenv qenv (p ⇉ ps)
  = do
      (p'env , q₁env) ← check-premise rules penv eenv qenv p
      _ ← check-premise-chain rules (penv ∙ p'env) eenv q₁env ps
      succeed tt

run-typerule : Rules → (rule : TypeRule) → ((subject rule) -Env) → Failable ⊤
run-typerule rules rule env = check-premise-chain rules ` ε env (proj₂ (premises rule))

-- check the precondition that the thing must be a type!
run-univrule : Rules → (rule : UnivRule) → ((input rule) -Env) → Failable ⊤
run-univrule rules@(rs t u ∋ e) rule env
  = do
     _ ← type-check rules t (termFrom (input rule) env)
     _ ← check-premise-chain rules env ε ` (proj₂ (premises rule))
     succeed tt

-- check the precondition that the type must actually be a type
run-∋rule : Rules → (rule : ∋rule) → ((input rule) -Env) → ((subject rule) -Env) → Failable ⊤
run-∋rule rules@(rs t u ∋ e) rule ienv senv
  = do
     _ ← type-check rules t (termFrom (input rule) ienv)
     _ ← check-premise-chain rules ienv ε senv (proj₂ (premises rule))
     succeed tt

run-erule : Rules                           →
            (rule : ElimRule)               →
            e-Env (ElimRule.target rule) 0  →
            (ElimRule.targetPat rule) -Env  →
            (ElimRule.eliminator rule) -Env →
            Failable (Term lib const 0) -- should this really be zero?!
-- TO DO - FIX THIS!            
run-erule rules rule e-env T-env s-env
  = do
      _ ← check-premise-chain rules T-env e-env s-env (proj₂ (premises rule))
      x ← form-output (output rule) 
      succeed (toTerm x e-env (output rule))
    where
      open ElimRule
      form-output : lcon (target rule) (proj₁ (premises rule)) 0 → Failable (proj₁ (premises rule) -Env)
      form-output (lcon.ess   x) = {!!}
      form-output (lcon.thunk x) = {!!}
      form-output (x lcon./  x₁) = {!!}

{-# TERMINATING #-}
univ-check rules  []              input
  = fail "univ-check: print the failing term here"
univ-check rules (urule ∷ urules) input
  with match-univrule urule input
... | nothing = univ-check rules urules input
... | just x with run-univrule rules urule x
... | succeed x₁ = succeed x₁
... | fail x₁ = univ-check rules urules input

type-check  rules []      ms
  = fail "type-check: print the failing term here"
type-check rules (trule ∷ trules) ms
  with match-typerule trule ms
... | nothing = type-check rules trules ms
... | just env with run-typerule rules trule env
... | succeed x = succeed x
... | fail x    = type-check rules trules ms


∋-check rules []               sub inp
  = fail "∋-check: print the failing term here"
∋-check rules (∋-rule ∷ ∋rules) sub inp
  with match-∋rule ∋-rule inp sub
... | nothing = ∋-check rules ∋rules sub inp
... | just (subj-env , input-envs) with run-∋rule rules ∋-rule subj-env input-envs
... | succeed x = succeed x
... | fail    x = ∋-check rules ∋rules sub inp

elim-synth : Rules                           →
             List ElimRule                   →
             (synth-type : Term lib const γ) →
             (eliminator : Term lib const γ) →
             Failable (Term lib const γ)
elim-synth rules []             T s = fail "elim-synth: print the failing term here"
elim-synth rules (erule ∷ erules) T s with match-erule erule T s
... | nothing              = elim-synth rules erules T s
... | just (T-env , s-env) = {!!} --run-erule rules erule {!!} T-env s-env

-- -- TO DO (afterwards clean up the STLC example unnecessary rules)

-- equality TODO - implement operational semantics and revisit this
-- At the moment, equality is just syntactic
eqfail : Failable ⊤
eqfail = fail "Equality failure."

_≡v_ : Var γ → Var γ → Failable ⊤
ze   ≡v ze    = succeed tt
su v ≡v su v' = v ≡v v'
_    ≡v _     = eqfail

_≡_ {ess} {const} (` x)    (` x₁) with x == x₁
... | false = eqfail
... | true  = succeed tt
_≡_ {ess} {const} (x ∙ x₁) (x₂ ∙ x₃) = do
                                         _ ← x  ≡ x₂
                                         _ ← x₁ ≡ x₃
                                         return tt
_≡_ {ess} {const} (bind x) (bind x') = x ≡ x'
_≡_ {ess} {const} _ _ = eqfail

_≡_ {ess} {compu} (var x) (var x')        = x ≡v x'
_≡_ {ess} {compu} (elim e s) (elim e' s') = do
                                              _ ← e ≡ e'
                                              _ ← s ≡ s'
                                              return tt
_≡_ {ess} {compu}  _          _           = eqfail

_≡_ {lib} {const} (ess x)    (ess x')  = x ≡ x'
_≡_ {lib} {const} (thunk x) (thunk x') = x ≡ x'
_≡_ {lib} {const}  _         _         = eqfail

_≡_ {lib} {compu} (ess x) (ess x')  = x ≡ x'
_≡_ {lib} {compu} (t ∷ T) (t' ∷ T') = do  -- maybe we can ignore the annotation here?
                                        _ ← t ≡ t'
                                        _ ← T ≡ T'
                                        return tt
_≡_ {lib} {compu}  _       _        = eqfail

infer : Rules → Context γ → Term lib compu γ → Failable (Term lib const γ)
infer rules Γ (ess (var x))    = succeed (x ‼V Γ)
infer rules@(rs t u ∋ ee) Γ (ess (elim e s)) = do
                             T ← infer rules Γ e
                             S ← elim-synth rules ee T s
                             succeed S
infer rules@(rs tr u ∋ e) Γ (t ∷ T)  = do
                   _ ← ∋-check rules ∋ t T
                   succeed T

check : Rules → Context γ → (type : Term lib const γ)  → (term : Term l d γ) → Failable ⊤
check {_} {lib} {const} rules@(rs t u ∋ e) Γ T (ess x)
  = do
      _ ← ∋-check rules ∋ (ess x) T
      succeed tt
check {_} {lib} {const} rules Γ T (thunk x)
  = do
      S ← infer rules  Γ (ess x)
      S ≡ T -- this is the gotcha, at the moment just syntactic equality-}
check {_} {ess} {const} rules@(rs tr u ∋ e) Γ T t = ∋-check rules ∋ (ess t) T
check {_} {ess} {compu} rules Γ T t = do
                                  S ← infer rules Γ (ess t)
                                  S ≡ T
check {_} {lib} {compu} rules Γ T t = do
                                  S ← infer rules Γ t
                                  S ≡ T
-- \end{code}
