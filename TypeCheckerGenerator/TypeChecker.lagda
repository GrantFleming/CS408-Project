\section{Checking types}
\label{section-checking-types}

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
that we might easily pass them around. We do so with the following type.

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

Firstly, we present three functions, one for checking each of the user
provided typing rules. Each definition proceeds in the same way,
attempting to match an appropriate rule, if a match is found, the rule is
run. If no rule is found to match, and there are no rules left to check,
these functions fail with a descriptive error.

\begin{code}
∋-check     :  Context γ              →
               RuleSet                →
               (term type : Const γ)  →
               Failable ⊤
              
type-check  :  Context γ          →
               RuleSet            →
               (type : Const γ)   →
               Failable ⊤

elim-synth : Context γ                           →
             RuleSet                             →
             (target-type eliminator : Const γ)  →
             Failable (Const γ)
\end{code}
\hide{
\begin{code}
univ-check  :  Context γ            →
               RuleSet              →
               (input : Const γ)    →
               Failable ⊤
\end{code}
}

We define a notion of term equivalence that we will need later in order
to check the type of computations embedded in constructions. This is a
purely syntactic action. If terms are to have their normal forms compared
then they must be normalized before checking their equivalence here.

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
check and infer. We check the type of constructions and infer the type of
computations, however since we can embed computations in constructions using
$thunk$ we may accept a call to check the type of any term.

When checking constructions, we make a distinction between two cases,
either we duck under a thunk to check the computation beneath it, or we
delegate immediately to \emph{∋-check}. When checking computations under a thunk,
we always start by synthesizing the type with a call to \emph{infer} safe in the
knowledge that if it succeeds, we are guaranteed that what is given is a type.
We then check equivalence between what was inferred, and the type we are checking
after normalising each of them.

When inferring the type of computations, there are three cases that we consider
seperately. The types of variables are looked up in the context. Terms with type
annotations are checked to determine that the annotation is indeed the type of
the term and if this is so then the normalised annotation is returned. Lastly,
the types of eliminations are inferred by synthesizing the type of the target
before delegating to \emph{elim-synth} so that it might determine to the appropriate
elimination typing rule to run. Any term given back in this process is checked to
be a type before $infer$ returns it.

\begin{code}
check  :  RuleSet            →
          Context γ          →
          (type : Const γ)   →
          (term : Term d γ)  →
          Failable ⊤
          
infer  :  RuleSet            →
          Context γ          →
          (term : Compu γ)   →
          Failable (Const γ)
\end{code}

Before we discuss the running of rule instances, we must first describe how
to check a premise chain. The result of matching against a given rule provides
us with the necessary environments for us to resolve the schematic variables
thay might exist in a premise. In our implementation checking the premises
turns out to be mostly trivial, if verbose. Each data constructor of a Premise
resolves to a calling a single function that we have already provided (such as 
\emph{type-check}, \emph{check} or \emph{\_≡ᵗ\_}) before building the required
environments for what what is newly trusted and what remains to be trused.

We provide just the definition for the '∈' premise by way of example here so that
might see how the concrete terms are realised from expressions and schematic
variables before we delegate to $check$.
\hide{
\begin{code}
check-premise-chain  :     RuleSet              →
                           ∀{γ} → Context γ     →
                           {p q p' : Pattern γ} →
                           p -Env → q -Env      →
                           Prems p q p'         →
                           Failable (p' -Env)
\end{code}
}
\begin{code}
check-premise : Context γ         →
                RuleSet           →
                p -Env → q -Env   →
                Prem p q γ p' q'  →
                Failable (p' -Env × q' -Env)

check-premise Γ rules penv qenv (T ∋' ξ [ θ ])
  = do
      _ ← check rules Γ (toTerm penv T) ((ξ ‼ qenv) ⟨term θ)
      succeed ((thing (ξ ‼ qenv)) , (qenv -penv ξ))
\end{code}
\hide{
\begin{code}
check-premise Γ rules penv qenv (type ξ θ)
  = do
    _ ← type-check  Γ rules ((ξ ‼ qenv) ⟨term θ)
    succeed (thing (ξ ‼ qenv) , (qenv -penv ξ))
check-premise Γ rules@(rs _ _ _ _ β η) penv qenv (x ≡' x')
  = do
      _ ← normalize η β (infer rules , check-premise-chain rules) Γ (` "unknown") (toTerm penv x)
        ≡ᵗ
        normalize η β (infer rules , check-premise-chain rules) Γ (` "unknown") (toTerm penv x')
      succeed (` , qenv)
check-premise Γ rules penv qenv (univ x)
  = do
      _ ← univ-check Γ rules (toTerm penv x)
      succeed (` , qenv)
check-premise Γ rules penv qenv (x ⊢' prem)
  = do
      (p'env , q'env) ← check-premise (Γ -, toTerm penv x) rules penv qenv prem
      succeed ((bind p'env) , q'env)

check-premise-chain _ _ penv _ (ε _)
  = succeed penv
check-premise-chain Γ rules penv qenv (prem ⇉ prems)
  = do
      (p'env , q'env) ← check-premise rules Γ penv qenv prem
      p''env ← check-premise-chain Γ rules (penv ∙ p'env) q'env prems
      succeed p''env
\end{code}
}
Checking a whole chain of premise proceeds as one might expect; each premise is
checked in order. The environments for the things we trust accumulate while the
environments for the things that remain to be trusted are whittled away. If the
premise chain is empty, we simply return what it is that we already trust.

In direct correspondance to our initial three functions that check the
various user defined rules, we provide three more, one for running each
type of rule should such a matching rule be found. We make sure to address
the appropriate conditions here, such as checking that the type in a $∋$
rule is indeed a type.

We give two examples here, that of running a $∋$ rule and one of running
an elimination rule. The first merely tries to succeed, the second must
return the synthesized type.

We do not request environments for the exact patterns in a rule, but instead
for their opening into the current scope. Similarly when we retrieve the
premise chain from a rule, we open this to the current scope before
checking it. This method allows us to mandate that rules are defined in the
empty scope while allowing them to be applied in any scope.

\begin{code}
run-∋rule  :  Context γ                    →
              RuleSet                      →
              (rule : ∋rule)               →
              ((γ ⊗ (input rule)) -Env)    →
              ((γ ⊗ (subject rule)) -Env)  →
              Failable ⊤
run-∋rule {γ} Γ rules ∋-rule input-env subject-env
  = do
      ty ← return (termFrom (input ∋-rule) input-env)
      _ ← type-check Γ rules ty
      chain ← return (⊗premises γ (proj₂ (premises ∋-rule)))
      _ ← check-premise-chain rules Γ input-env subject-env chain                     
      succeed tt

run-erule : Context γ                   →
            RuleSet                     →
            (rule : ElimRule)           →
            (γ ⊗ targetPat rule)  -Env  →
            (γ ⊗ eliminator rule) -Env  →
            Failable (Const γ)
run-erule {γ} Γ rules elim-rule input-env subject-env
  = do
      chain ← return (⊗premises γ (proj₂ (premises elim-rule)))
      p'env ← check-premise-chain rules Γ input-env subject-env chain
      elim-ty ← return (toTerm p'env (output elim-rule))
      _ ← type-check Γ rules elim-ty
      succeed elim-ty
\end{code}
Our typechecking process is a highly mutually recursive process by nature. We can
leverage Agda's termination checker to give us feedback which we might use to
guarantee that the process terminates. We are unable to guarantee termination with
in this case as we do not impose the required restrictions on user supplied rules. If
a user supplies a rule containing a circular check, then the type checking
process will not halt. We talk more about this limitation later in our evaluation
of the software.
\hide{
\begin{code}
run-univrule : Context γ → RuleSet → (rule : UnivRule) → ((γ ⊗ (input rule)) -Env) → Failable ⊤
run-univrule {γ = γ} Γ rules@(rs t u ∋ e β η) rule env
  = do
     _ ← type-check Γ rules (termFrom (input rule) env)
     _ ← check-premise-chain rules Γ env ` (⊗premises γ (proj₂ (premises rule)))
     succeed tt

run-typerule : Context γ → RuleSet → (rule : TypeRule) → ((γ ⊗ (subject rule)) -Env) → Failable ⊤
run-typerule {γ} Γ rules rule env
  = do
      _ ← check-premise-chain rules Γ ` env (⊗premises γ (proj₂ (premises rule)))
      succeed tt


{-# TERMINATING #-}
univ-check Γ rules@(rs _ u _ _ _ _) input = univ-check' u
  where
    univ-check' : List UnivRule → Failable ⊤
    univ-check' []
      = fail ("univ-check: " ++ (print input) ++ " is not a universe")
    univ-check' (urule ∷ urules)
      with match-univrule urule input
    ... | nothing = univ-check' urules
    ... | just x = run-univrule Γ rules urule x

type-check Γ rules (thunk x)
  = do
      ty ← infer rules Γ x
      univ-check Γ rules ty
type-check  Γ rules@(rs t _ _ _ _ _) ms = type-check' t
  where
    type-check' : List TypeRule → Failable ⊤
    type-check'  []
      = fail ("failed type-check: " ++ (print ms) ++ " is not a type")
    type-check' (trule ∷ trules)
      with match-typerule trule ms
    ... | nothing = type-check' trules
    ... | just env = run-typerule Γ rules trule env

∋-check Γ rules sub (` "set") = type-check Γ rules sub
∋-check Γ rules@(rs _ _ ∋ _ _ _) sub inp = ∋-check' ∋
  where
    ∋-check' : List ∋rule → Failable ⊤
    ∋-check' []
      = fail ("failed ∋-check: " ++ (print inp) ++ " is not the type of " ++ (print sub))
    ∋-check' (∋-rule ∷ ∋rules)
      with match-∋rule ∋-rule inp sub
    ... | nothing = ∋-check' ∋rules
    ... | just (subj-env , input-envs) = run-∋rule Γ rules ∋-rule subj-env input-envs


elim-synth {γ} Γ rules@(rs _ _ _ e _ _) T s = elim-synth' e
  where
    elim-synth' : List ElimRule → Failable (Const γ)
    elim-synth' []
      = fail ("elim-synth: failed to match elimination rule for target = " ++ (print T) ++ " and eliminator = " ++ (print s))
    elim-synth' (erule ∷ erules) with match-erule erule T s
    ... | nothing              = elim-synth' erules
    ... | just (T-env , s-env) = run-erule Γ rules erule T-env s-env


infer rules@(rs _ _ _ _ β η) Γ (var x)    = do
                             ty ← return (x ‼V Γ)
                             tyn ← return (normalize η β (infer rules , check-premise-chain rules) Γ (` "set") ty)
                             _ ← type-check Γ rules tyn
                             succeed tyn
infer rules@(rs _ _ _ _ β η) Γ (elim e s) = do
                             T ← infer rules Γ e
                             S ← elim-synth Γ rules T s
                             Sn ← return (normalize η β (infer rules , check-premise-chain rules) Γ (` "set") S)      
                             succeed Sn
infer rules@(rs _ _ _ _  β η) Γ (t ∷ T)  = do
                   Tn ← return (normalize η β (infer rules , check-premise-chain rules) Γ (` "set") T)
                   _ ← ∋-check Γ rules t Tn
                   succeed Tn

-- special case, checking if (type ∈ tm) is checking if tm is a type
check rules@(rs t _ _ _ _ _) Γ (` "set") tm = type-check Γ rules (↠↠ tm)

check {_} {const} rules Γ T (thunk x)  = check rules Γ T x
check {_} {const} rules Γ T t          = ∋-check Γ rules t T
check {_} {compu} rules@(rs _ _ _ _ β η) Γ T t = do
                            S ← infer rules Γ t
                            normalize η β ((infer rules) , check-premise-chain rules) Γ (` "set") S
                              ≡ᵗ
                              normalize η β ((infer rules) , check-premise-chain rules) Γ (` "set") T
\end{code}
}
\usebox{\rules}

