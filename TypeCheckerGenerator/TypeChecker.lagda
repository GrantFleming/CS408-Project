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
open import Rules using (ConstRule; match-rule; menv)
import Pattern as Pat
open Pat using (Pattern; _-Env)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec)
open import Data.Vec.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
import Judgement
open Judgement.Judgement using (input)
\end{code}

\begin{code}
private
  variable
    γ : Scope
    p : Pattern 0
    n : ℕ

open ConstRule


run-crule : -- the rule we want to run
            (rule : ConstRule) →                    
            -- the pattern environment from matching the subject
            menv rule →
            -- the pattern environments from matching the inputs
            All _-Env (input (conclusion rule)) →
            -- succeed tt if the rule ran successfully otherwise fail
            Failable ⊤
run-crule rule sub inp = {!!}

const-check : List ConstRule                →
              (subject : Maybe (Lib-Const γ))       →
              (inputs : Vec (Lib-Const γ) n) →
              Failable ⊤
const-check []             sub inp = fail "Print the failing term here"
const-check (rule ∷ rules) sub inp with match-rule rule sub inp 
... | nothing = const-check rules sub inp
... | just (subj-env , input-envs) with run-crule rule subj-env input-envs
... | succeed x = succeed x
... | fail    x = const-check rules sub inp

-- There are certain rules that exist regardless of the type theory
-- We approach these differently, while in Rules.lagda, we gave the machinery for creating
-- rules of a specific 'form' , here these are actual rules to be applied to syntax.
-- Thus these don't necessarily take the 'form' of rules, the are just functionality.

-- There are two globally presented rules (rules which explicitly talk about the context)
-- There are context extension and type lookup. This functionality is in Context.lagda
-- given by _,_ for context extension and loopup for type lookup

-- you can synthesize the type of a variable by just looking it up in the context using lookup


-- you can synthesize the type of anything with a type annotation if the annotation is indeed a
-- type and and we can check the annotated thing at that type
radical : Lib-Const γ → Lib-Const γ → Failable (Term lib const γ)
radical (ess t)   (ess T)   = {!!}
radical (ess t)   (thunk T) = {!!}
radical (thunk t) (ess T)   = {!!}
radical (thunk t) (thunk T) = {!!}

-- you can embed synthesizable things in checkable things

-- TO DO

-- if n is in a Universe then it is a type

-- TO DO (afterwards clean up the STLC example unnecessary rules)

-- reflexivity

-- TO DO

-- These rules are stored together in some structure

-- TO DO
-- we have introduction rules
-- and seperately we have elimination rules

infer : Term lib compu γ → Failable (Term lib const γ)
infer (ess x)  = {!!}
infer (t ∷ T)  = radical t T

\end{code}
