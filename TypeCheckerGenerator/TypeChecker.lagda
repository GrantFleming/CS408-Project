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
open Pat using (Pattern; _-Env; _∙_; thing; `; bind; s-scope; svar; _‼_; _-penv_)
open Pat.Expression using (Expression; Expr; lcon; toTerm; e-Env; _^eenv)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Vec.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Judgement using (J-Type; TY; NI; UNI)
open Judgement.Judgement using (input)
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
    

open ConstRule


∋-check : List ConstRule                  →
          (subject : Maybe (Lib-Const γ)) →
          (inputs : Vec (Lib-Const γ) n)  →
          Failable ⊤

type-check : List ConstRule                  →
             (subject : Maybe (Lib-Const γ)) →
             Failable ⊤

univ-check : List ConstRule →
             Lib-Const γ    →
             Failable ⊤

_≡_ : Term l d γ → Term l d γ → Failable ⊤







-- TO-DO - store each kind of rule seperatly (∋, TYPE and UNIV)
c-rules : List ConstRule
c-rules = []

e-rules : List ElimRule
e-rules = []

check-premise : (proj₂ s) -Env    →
                e-Env (proj₁ s) γ →
                q -Env            →
                Prem s q γ p' q'  →
                Failable (p' -Env × q' -Env)
check-premise penv γenv qenv (type ξ θ)
  = do
      _ ← type-check c-rules (just ((ξ ‼ qenv) ⟨term θ))
      succeed (thing (ξ ‼ qenv) , (qenv -penv ξ))
check-premise penv γenv qenv (T ∋' ξ [ θ ])
  = do
    _ ← ∋-check c-rules (just ((ξ ‼ qenv) ⟨term θ )) (toTerm penv γenv T ∷ [])
    succeed (thing (ξ ‼ qenv) , (qenv -penv ξ))
check-premise penv γenv qenv (x ≡' x')
  = do
    _ ← toTerm penv γenv x ≡ toTerm penv γenv x'
    succeed (` , qenv)
check-premise penv γenv qenv (univ x)
  = do
    _ ← univ-check c-rules (toTerm penv γenv x)
    succeed (` , qenv)
check-premise penv γenv qenv (x ⊢' p)
  = do
    (p'env , q'env) ← check-premise penv (γenv ^eenv) qenv p
    succeed (bind p'env , q'env)

check-premise-chain : p -Env → e-Env δ 0 → q -Env → Prems δ p q p' → Failable ⊤
check-premise-chain penv eenv qenv (ε x)    = succeed tt
check-premise-chain penv eenv qenv (p ⇉ ps) = do
                                            (p'env , q₁env) ← check-premise penv eenv qenv p
                                            _ ← check-premise-chain (penv ∙ p'env) eenv q₁env ps
                                            succeed tt

run-crule : -- the rule we want to run
            (rule : ConstRule) →                    
            -- the pattern environment from matching the subject
            menv rule →
            -- the pattern environments from matching the inputs
            All _-Env (input (conclusion rule)) →
            -- succeed tt if the rule ran successfully otherwise fail
            Failable ⊤
{-
  This will have two steps, failure at each step propagates:
    1) Check the preconditions
    2) Check the premise chain
  These rules only cover TYPE, ∋ and UNIV so they don't have post conditions
-}            
run-crule rule sub inp = do
                           _ ← check-preconditions rule inp
                           _ ← check-premisechain rule sub
                           succeed tt
  where
    check-preconditions : (rule : ConstRule) → All _-Env (input (conclusion rule)) → Failable ⊤
    check-preconditions rule envs = {!!}
    check-premisechain : (rule : ConstRule) → menv rule → Failable ⊤
    check-premisechain rule env = {!!}


run-erule : (rule : ElimRule) →
            (ElimRule.targetPat rule) -Env →
            (ElimRule.eliminator rule) -Env →
            Failable (Term lib const γ)
{-
  This will involve steps
    1) Check the premise chain
    2) Form the output
    3) Convert the output from an Expr to a Term
-}
run-erule rule T-env s-env = {!!}

univ-check  []            t = fail "univ-check: print the failing term here"
univ-check (rule ∷ rules) t with match-crule rule UNI nothing (t ∷ [])
... | nothing = univ-check rules t
... | just (subj-env , input-envs) with run-crule rule subj-env input-envs
... | succeed x = succeed x
... | fail x = univ-check rules t

type-check  []            ms = fail "type-check: print the failing term here"
type-check (rule ∷ rules) ms with match-crule rule TY ms []
... | nothing = type-check rules ms
... | just (subj-env , input-envs) with run-crule rule subj-env input-envs
... | succeed x = succeed x
... | fail x    = type-check rules ms


∋-check []             sub inp = fail "∋-check: print the failing term here"
∋-check (rule ∷ rules) sub inp with match-crule rule NI sub inp 
... | nothing = ∋-check rules sub inp
... | just (subj-env , input-envs) with run-crule rule subj-env input-envs
... | succeed x = succeed x
... | fail    x = ∋-check rules sub inp

elim-synth : List ElimRule →
             (synth-type : Term lib const γ) →
             (eliminator : Term lib const γ) →
             Failable (Term lib const γ)
elim-synth []             T s = fail "elim-synth: print the failing term here"
elim-synth (rule ∷ rules) T s with match-erule rule T s
... | nothing              = elim-synth rules T s
... | just (T-env , s-env) = run-erule rule T-env s-env

-- TO DO (afterwards clean up the STLC example unnecessary rules)

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

infer : Context γ → Term lib compu γ → Failable (Term lib const γ)
infer Γ (ess (var x))    = succeed (x ‼V Γ)
infer Γ (ess (elim e s)) = do
                             T ← infer Γ e
                             S ← elim-synth e-rules T s
                             succeed S
infer Γ (t ∷ T)  = do
                   _ ← ∋-check c-rules (just t) (T ∷ [])
                   succeed T

check : Context γ → (type : Term lib const γ)  → (term : Term l d γ) → Failable ⊤
check {_} {lib} {const} Γ T (ess x)
  = do
      _ ← ∋-check c-rules (just (ess x)) (T ∷ [])
      succeed tt
check {_} {lib} {const} Γ T (thunk x)
  = do
      S ← infer Γ (ess x)
      S ≡ T -- this is the gotcha, at the moment just syntactic equality-}
check {_} {ess} {const} Γ T t = ∋-check c-rules (just (ess t)) (T ∷ [])
check {_} {ess} {compu} Γ T t = do
                                  S ← infer Γ (ess t)
                                  S ≡ T
check {_} {lib} {compu} Γ T t = do
                                  S ← infer Γ t
                                  S ≡ T

\end{code}
