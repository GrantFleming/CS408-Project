\section{Checking Types}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module TypeChecker where
\end{code}

\begin{code}
open import CoreLanguage
open import Failable
open import Data.Maybe using (just; nothing)
open import Context using (Context; _‼V_) renaming (_,_ to _-,_)
open import Data.List using (List; []; _∷_)
open import Rules
open import Pattern using (Pattern; _-Env; _∙_; thing; `; bind; _‼_; _-penv_; _⊗_; termFrom)
open import Expression using (toTerm)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Data.String using (_==_)
open import Data.Bool using (true; false)
open import Data.Product using (_×_; proj₁; proj₂)
open import Thinning using (_⟨term_)
open import Data.String using (_++_)
open import Semantics
open import EtaRule using (η-Rule)
\end{code}
}
\hide{
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
open ElimRule
\end{code}
}

We now have all of the required definitions to construct the process of
typechecking. This process is a set of mutually recursive definitions which
we will describe here.

When we check types, it is convenient to collect all the rules together so
that we might easily pass them around. We do so will the following type.

\begin{code}
data RuleSet : Set where
  rs : List TypeRule  →
       List UnivRule  →
       List ∋rule     →
       List ElimRule  →
       List β-rule    →
       List η-Rule    →
       RuleSet
\end{code}


Firstly, we present four functions, one for checking each of the user
provided typing rules. We must provide the list of specific rule types
alongside the complete structure of all rules so that we might recurse
over this list when looking for a matching rule while keeping the entire
collection of rules whole for the purpose of providing it to other
functions as may be required. Each definition proceeds in the same way,
attempting to match an appropriate rule, if a match is found, the rule is
run. We will explore what it means to run a rule later. If no rule is
found to match, and there are no rules left to check, these functions
fail with a descriptive error.

\begin{code}
∋-check     :  Context γ            →
               RuleSet                →
               List ∋rule           →
               (subject : Const γ)  →
               (input : Const γ)    →
               Failable ⊤
              
type-check  :  Context γ            →
               RuleSet                →
               List TypeRule        →
               (subject : Const γ)  →
               Failable ⊤
              
univ-check  :  Context γ            →
               RuleSet                →
               List UnivRule        →
               (input : Const γ)    →
               Failable ⊤

elim-synth : Context γ                    →
             RuleSet                        →
             List ElimRule                →
             (synth-type : Term const γ)  →
             (eliminator : Term const γ)  →
             Failable (Term const γ)
\end{code}

We define a notion of equivalence of terms that we will need in order
to embed inferrable terms into checkable terms. This process involves
synthesizing a type for a term before ascertaining if it is equivalent
to the type we are checking the term at. This is a purely syntactic action.
If terms are to have their normal forms compared then they must be
normalized before checking their equivalence here.

\begin{code}
_≡v_ : Var γ → Var γ → Failable ⊤
_≡ᵗ_ : Term d γ → Term d γ → Failable ⊤
\end{code}
\hide{
\begin{code}
eqfail : Failable ⊤
eqfail = fail "Equality failure."


ze   ≡v ze    = succeed tt
su v ≡v su v' = v ≡v v'
_    ≡v _     = eqfail
\end{code}
}
\hide{
\begin{code}
_≡ᵗ_ {const} (` x)    (` x₁) with x == x₁
... | false = fail ("Equivalence failure: " ++ x ++ " ≠ " ++ x₁)
... | true  = succeed tt
_≡ᵗ_ {const} (x ∙ x₁) (x₂ ∙ x₃) = do
                                    _ ← x  ≡ᵗ x₂
                                    _ ← x₁ ≡ᵗ x₃
                                    return tt
_≡ᵗ_ {const} (bind x)  (bind x')   = x ≡ᵗ x'
_≡ᵗ_ {const} (thunk x) (thunk x')  = x ≡ᵗ x'

_≡ᵗ_ {compu} (var x) (var x')        = x ≡v x'
_≡ᵗ_ {compu} (elim e s) (elim e' s') = do
                                        _ ← e ≡ᵗ e'
                                        _ ← s ≡ᵗ s'
                                        return tt
_≡ᵗ_ {compu} (t ∷ T) (t' ∷ T') = do
                                   _ ← t ≡ᵗ t'
                                   return tt
τ₁ ≡ᵗ τ₂  = fail ("Equivalence failure: " ++ print τ₁ ++ " ≠ " ++ print τ₂)
\end{code}
}

The high level functionality of our type checker is given by two functions,
check and infer. In general, we check constructions and infer computations,
however since we can embed inferrable terms in checkable terms we may accept
a call to check the type of any term.

When checking constructions, we only make the distinction of two cases,
either we duck under a thunk to check the computation beneath it, or we
call to $∋-check$ otherwise. When checking computations, we always start
by synthesizing the type with a call to $infer$ safe in the knowledge that
if it succeeds, we are guaranteed that what is given is a type. We then check
equivalence between what was inferred, and the type we are checking as
described above.

When inferring computations, the type of variables are looked up in the
context. We check to ensure that what we got from the context was indeed
a type before returning it. Terms with type annotations have their
type checked against their annotation, the annotation is verified as being
a type in this process, and the annotation is returned. Eliminations are
checked by synthesizing the type of the target before delegating to $elim-synth$
so that it might check the elimination rules. Any term given back in this
process is checked to be a type before $infer$ returns it.

\begin{code}
check  :  RuleSet                   →
          Context γ               →
          (type : Term const γ)   →
          (term : Term d γ)       →
          Failable ⊤
          
infer  :  RuleSet                  →
          Context γ              →
          (term : Term compu γ)  →
          Failable (Term const γ)
\end{code}

We now introduce the ability to check a chain of premises. The result of
matching against a given rule provides us with the necessary environments
in which we can get concrete terms from the schematic variables and
expressions in our premise. In our implementation checking the premise
turns out to be mostly trivial, if verbose. Each data constructor of a Premise
maps nicely to functionality we have already provided - such as $type-check$,
$univ-check$ and $\_≡ᵗ\_$. We provide just the definition for the $∈$ premise
by way of example here.

Here we delegate to check, creating a concrete type to check from the
expression $T$, and looking up the term we are checking using the schematic
variable $ξ$, thinning it appropriately. A successful checking of a premise
results in environments for the patterns determining what is newly
trusted and what is left to be trusted.

The checking of a whole chain of premise proceeds as one might expect.
Each premise is checked in order. The environments for the things we trust
accumulate while the environments for the things that remain to be trusted
are whittled away. It is expected that these functions are called with
the opened premise chain, they will not open the chain to the scope in
which we are currently operating.

\begin{code}
check-premise : Context γ   →
                RuleSet       →
                p -Env      →
                q -Env      →
                Prem p q γ p' q'  →
                Failable (p' -Env × q' -Env)

check-premise-chain  :     RuleSet           →
                           Context γ         →
                           {p : Pattern γ}
                           {q : Pattern γ}
                           {p' : Pattern γ}  →
                           p -Env            →
                           q -Env            →
                           Prems p q p'      →
                           Failable (p' -Env)
--...
check-premise Γ rules penv qenv (T ∋' ξ [ θ ])
  = do
    _ ← check rules Γ (toTerm {γ = 0} penv T) ((ξ ‼ qenv) ⟨term θ)
    succeed ((thing (ξ ‼ qenv)) , (qenv -penv ξ))
--...
\end{code}
\hide{
\begin{code}
check-premise {q = q} Γ rules@(rs t u ∋ e β η) penv qenv (type ξ θ)
  = do
    _ ← type-check  Γ rules t ((ξ ‼ qenv) ⟨term θ)
    succeed (thing (ξ ‼ qenv) , (qenv -penv ξ))

check-premise Γ rules@(rs t u ∋ e β η) penv qenv (x ≡' x')
  = do
    _ ← normalize η β ((infer rules) , λ scp → check-premise-chain {γ = scp} rules) Γ (` "unknown") (toTerm penv x)
      ≡ᵗ
      normalize η β ((infer rules) , λ scp → check-premise-chain {γ = scp} rules) Γ (` "unknown") (toTerm penv x')
    succeed (` , qenv)
check-premise Γ rules@(rs t u ∋ e β η) penv qenv (univ x)
  = do
    _ ← univ-check Γ rules u (toTerm {γ = 0} penv x)
    succeed (` , qenv)
check-premise {γ = γ} Γ rules penv qenv (x ⊢' prem)
  = do
    (p'env , q'env) ← check-premise (Γ -, toTerm {γ = 0} penv x) rules penv qenv prem
    succeed ((bind p'env) , q'env)
\end{code}
}
\hide{
\begin{code}
check-premise-chain Γ rules penv qenv (ε x)       = succeed penv
check-premise-chain Γ rules penv qenv (prem ⇉ prems)
 = do
     (p'env , q₁env) ← check-premise rules Γ penv qenv prem
     p''env ← check-premise-chain Γ rules (penv ∙ p'env) q₁env prems
     succeed p''env
\end{code}
}

In direct correspondance to our initial four functions that check the
various user defined rules, we provide four more, one for running each
type of rule should such a matching rule be found. We make sure to address
the appropriate conditions here, such as checking that the type in a $∋$
rule is indeed a type.

We give two examples here, that of running a $∋$ rule and one of running
an elimination rule. The first merely tries to succeed, the second must
return the synthesized type.

There are several things worth noting here. Firstly that we do not take
environments for the Patterns in a rule, but for their opening into
the current scope. Similarly when we retrieve the premise chain from
the rule, we open this to the current scope before checking. This method
allows us to mandate that rules are defined in the empty scope but can
be applied in any scope.

We may also see here how it is that we build concrete terms from
expressions in the rules using $toTerm$ and from patterns and
environments using $termFrom$. The latter allows us to construct
the $T$ in $T ∋ t$ while the former is responsible for constructing
the output of running the elimination rule.

\begin{code}
run-∋rule  :  Context γ                    →
              RuleSet                        →
              (rule : ∋rule)               →
              ((γ ⊗ (input rule)) -Env)    →
              ((γ ⊗ (subject rule)) -Env)  →
              Failable ⊤
run-∋rule {γ} Γ rules@(rs t u ∋ e β η) rule ienv senv
  = do
     _ ← type-check Γ rules t
                    (termFrom (input rule) ienv)
     _ ← check-premise-chain  rules Γ ienv senv
                    (⊗premises γ (proj₂ (premises rule)))
     succeed tt

run-erule : Context γ                       →
            RuleSet                           →
            (rule : ElimRule)               →
            (γ ⊗ targetPat rule)  -Env →
            (γ ⊗ eliminator rule) -Env →
            Failable (Term const γ)
run-erule {γ} Γ rules rule T-env s-env
  = do
      p'env ← check-premise-chain rules Γ T-env s-env
                    (⊗premises γ (proj₂ (premises rule)))
      succeed (toTerm p'env (output rule))
\end{code}

There are similar such functions for running other rules, they all involve
checking the premise chain and occassionally other preconditions. Post-conditions
are not checked by these rules but are the responsibility of the caller.

This process is a highly mutually recursive process by nature. Agda's termination
checker allows us to be assured that we have not gotten ourselves into trouble
while constructing this system of functions.

\hide{
\begin{code}
run-univrule : Context γ → RuleSet → (rule : UnivRule) → ((γ ⊗ (input rule)) -Env) → Failable ⊤
run-univrule {γ = γ} Γ rules@(rs t u ∋ e β η) rule env
  = do
     _ ← type-check Γ rules t (termFrom (input rule) env)
     _ ← check-premise-chain rules Γ env ` (⊗premises γ (proj₂ (premises rule)))
     succeed tt

run-typerule : Context γ → RuleSet → (rule : TypeRule) → ((γ ⊗ (subject rule)) -Env) → Failable ⊤
run-typerule {γ} Γ rules rule env
  = do
      _ ← check-premise-chain rules Γ ` env (⊗premises γ (proj₂ (premises rule)))
      succeed tt


{-# TERMINATING #-}
univ-check Γ rules  []              input
  = fail ("univ-check: " ++ (print input) ++ " is not a universe")
univ-check Γ rules (urule ∷ urules) input
  with match-univrule urule input
... | nothing = univ-check Γ rules urules input
... | just x = run-univrule Γ rules urule x

type-check Γ rules@(rs t u ∋ e β η) trs (thunk x)
  = do
      ty ← infer rules Γ x
      univ-check Γ rules u ty
type-check  Γ rules []      ms
  = fail ("type-check: " ++ (print ms) ++ " is not a type")
type-check Γ rules (trule ∷ trules) ms
  with match-typerule trule ms
... | nothing = type-check Γ rules trules ms
... | just env = run-typerule Γ rules trule env

∋-check Γ rules@(rs t u ∋ e β η) _ sub (` "set") = type-check Γ rules t sub
∋-check Γ rules []               sub inp
  = fail ("failed ∋-check: " ++ (print inp) ++ " ∋ " ++ (print sub))
∋-check Γ rules (∋-rule ∷ ∋rules) sub inp
  with match-∋rule ∋-rule inp sub
... | nothing = ∋-check Γ rules ∋rules sub inp
... | just (subj-env , input-envs) = run-∋rule Γ rules ∋-rule subj-env input-envs


elim-synth Γ rules []             T s
  = fail ("elim-synth: failed to match elimination rule for target = " ++ (print T) ++ " and eliminator = " ++ (print s))
elim-synth Γ rules (erule ∷ erules) T s with match-erule erule T s
... | nothing              = elim-synth Γ rules erules T s
... | just (T-env , s-env) = run-erule Γ rules erule T-env s-env


infer rules@(rs t u ∋ ee β η) Γ (var x)    = do
                            -- check postcondition:
                             ty ← return (x ‼V Γ)
                             tyn ← return (normalize η β (infer rules , (λ scp → check-premise-chain {γ = scp} rules)) Γ (` "Type") ty)
                             _ ← type-check Γ rules t tyn
                             succeed tyn
infer rules@(rs t u ∋ ee β η) Γ (elim e s) = do
                             T ← infer rules Γ e
                             S ← elim-synth Γ rules ee T s
                             Sn ← return (normalize η β (infer rules , (λ scp → check-premise-chain {γ = scp} rules)) Γ (` "Type") S)      
                             -- check postcondition:
                             _ ← type-check Γ rules t Sn
                             succeed Sn
infer rules@(rs tr u ∋ e β η) Γ (t ∷ T)  = do
                   -- postcondition checks in ∋-check
                   Tn ← return (normalize η β (infer rules , (λ scp → check-premise-chain {γ = scp} rules)) Γ (` "Type") T)
                   _ ← ∋-check Γ rules ∋ t Tn
                   succeed Tn

-- special case, checking if (type ∈ tm) is checking if tm is a type
check {_} {const} rules@(rs t _ _ _ _ _) Γ (` "set") tm = type-check Γ rules t tm
check {_} {compu} rules@(rs t _ _ _ _ _) Γ (` "set") tm = type-check Γ rules t (thunk tm)

check {_} {const} rules Γ T (thunk x)         = check rules Γ T x
check {_} {const} rules@(rs tr u ∋ e β η) Γ T t = ∋-check Γ rules ∋ t T
check {_} {compu} rules@(rs tr u ∋ e β η) Γ T t = do
                            S ← infer rules Γ t
                            normalize η β ((infer rules) , λ scp → check-premise-chain {γ = scp} rules) Γ (` "Type") S
                              ≡ᵗ
                              normalize η β ((infer rules) , λ scp → check-premise-chain {γ = scp} rules) Γ (` "Type") T
\end{code}
}

