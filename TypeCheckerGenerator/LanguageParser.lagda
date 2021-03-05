\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module LanguageParser where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Pattern using (Pattern; `; _∙_; bind; place; ⊥; _⊗_)
open import Data.String using (String; words) renaming (_++_ to _+_; length to strlen)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Char using (Char; isAlpha; isDigit; isSpace; _==_)
open import Data.List using (List; _∷_; []; any; _++_; length; concat) renaming (map to lmap; foldr to lfoldr)
open import Data.Nat using (ℕ; suc; zero; _<ᵇ_)
open import Data.Nat.Show 
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Bool using (if_then_else_)
open import Function using (_∘′_)
open import Parser
open Parser.Parser
open Parser.Parsers
open parserstatemonad hiding (_⊗_)
import Data.Tree.AVL.Map as MapMod
open MapMod <-strictTotalOrder-≈
open import Thinning using (Weakenable; weaken; Thinnable; _⟨var_)
open import Rules using (TypeRule; ∋rule; ElimRule)
open TypeRule renaming (subject to tysub)
open ∋rule renaming (subject to ∋sub)
open ElimRule using (eliminator)
open import Data.Unit using (⊤; tt)
\end{code}
}

\hide{
\begin{code}
private
  variable
    δ : Scope
    γ : Scope
    A : Set
\end{code}
}
https://en.wikipedia.org/wiki/Left_recursion

Here we are having trouble with a non-terminating parser since any pattern with
a left-most 'place' may cause infinite recursion depending on the orders of the
rules. This is most plainly seen in the simple case of trying to parse the pattern
*place . ` "->" . place* say in the case of a function type. First it knows it must
parse some term for the place, and so it starts iterating through the rules,
potentially coming across the same rule again ad infinitum.

Clearly iterating over the rules trying to parse each one in turn is not the
best way to try to parse the language. Is there another way?

Well apparently patterns form a lattice. That is to say that every set of patterns
has a pattern we know as the "greatest lower bound" or infimum. This is a pattern
where any term that matches it also matches every term in the set of patterns, and
that there is no more 'specific' pattern which will do the same job. Note that this
pattern could be unmatchable! I wonder if this could help with my problem.

We can imagine a partial ordering where more specific patterns are less than more
general patterns, those which describe an atom are very specific, only one thing
matches this pattern, the ⊥ pattern is so specific nothing matches! The most general
pattern for a given scope is (place ι) since this matches anything (so long as
it is scoped correctly). So we may imagine some ordering as follows:


      ....          ...
⊥ ≤ ` "atoms"    ≤  ...  ≤ (place ι)
    ` "things"      ...
      ...

Where the important point to remember is for some $p ≤ p'$ then anything that
matches the pattern $p$ must also match $p'$.

So we will thus firstly define infimum below:

\begin{code}
module PatternLattice where

  -- TO DO - move to Pattern
  
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Data.String using (_≟_)
  open import Relation.Nullary using (yes; no)
  open import Data.Nat using (_≤?_)
  open import Thinning using (_O; ι)

  {-# TERMINATING #-}
  _∨_ : Pattern δ → Pattern δ → Pattern δ
  _∨_ (` x₁) (` x₂) with x₁ ≟ x₂
  ... | yes refl = ` x₁
  ... | no neq   = ⊥
  _∨_ (` x) (place x₁) = ` x
  _∨_ (p₁ ∙ p₂) (p₃ ∙ p₄) = p₁ ∨ p₃ ∙ p₂ ∨ p₄
  _∨_ (p₁ ∙ p₃) (place x) = p₁ ∨ (place x) ∙ p₃ ∨ (place x)
  _∨_ (bind p₁) (bind p₂) = bind (p₁ ∨ p₂)
  _∨_ (bind p₁) (place x) = bind (p₁ ∨ (place (x O)))
  _∨_ (place x) (` x₁)    = ` x₁
  _∨_ (place x) (p₂ ∙ p₃) = (place x) ∨ p₂ ∙ (place x) ∨ p₃
  _∨_ (place x) (bind p₂) = bind ((place (x O)) ∨ p₂)
  _∨_ (place {δ} x) (place {δ'} x₁) with δ ≤? δ'
  ... | yes relf = place x
  ... | no  neq  = place x₁
  _∨_ _  _  = ⊥
  infixl 30 _∨_

  testr : Pattern 0
  testr = (` "y" ∙ bind (` "pop")) ∨ (` "x" ∙ bind (place ι))
open PatternLattice hiding (_∨_)
test' = testr
\end{code}

Now the question is, how can we use this to fix our parsing problem?



\begin{code}
open import Data.Bool using (Bool; _∨_; not; _∧_)

disallowed-chars : List Char
disallowed-chars = '(' ∷ ')' ∷ ':' ∷ []

isendchar : Char → Bool
isendchar c = isSpace c ∨ any (c ==_) disallowed-chars

token : Parser String
token = until isendchar

idchar : Char → Bool
idchar c = not (any (c ==_) disallowed-chars) ∧ not (isSpace c)

identifier : Parser String
identifier = stringof idchar

\end{code}

\begin{code}
VarMap : Scoped
VarMap γ = Map (Var γ)

_⟨_ : Thinnable VarMap
vm ⟨ θ = map (_⟨var θ) vm

_^ : Weakenable VarMap
_^ = weaken _⟨_

fresh : String → VarMap γ → VarMap (suc γ)
fresh name vm = insert name ze (vm ^)
\end{code}

\begin{code}

Rules : Set
Rules = List TypeRule × List ∋rule × List ElimRule

TermParser : Scoped → Set
TermParser A = Rules → ∀ {γ} → VarMap γ → Parser (A γ)

\end{code}



\begin{code}
{-
longest : List (Const γ × String) → Maybe (Const γ × String)
longest [] = nothing
longest (x ∷ []) = just x
longest (x@(tm , s) ∷ xs) with longest xs
... | nothing = just x
... | just x'@(tm' , s') = just (if strlen s <ᵇ strlen s' then x else x')

computation : TermParser Compu
constructions : ℕ → TermParser (λ γ → List (Const γ × String))



pats : Pattern δ → ℕ → TermParser (λ γ → List (Const γ × String))
pats (` x) n rls vm = do
                           tok ← token
                           just (at , rest) ← return (complete (string x) tok)
                             where nothing → fail
                           return ((` at , rest) ∷ [])
pats (s ∙ t) n rls vm = do
                           ls ← pats s n rls vm
                           return ls
                           {-options ← return (lmap (λ (tm , s) → tm , (ws+nl >> pats t n rls vm) s) ls)
                           guaranteed-options ← return (lfoldr (λ where
                                                                 (tm , nothing) y → y
                                                                 (tm , just x) y → (tm , x) ∷ y)
                                                                 [] options)                      
                           aspairs ← return (lfoldr (λ (l , rs , _) done → lmap (λ (tm , s) → (l ∙ tm , s)) rs ++ done) [] guaranteed-options)
                           return aspairs-}
pats (bind t) n rls vm = do
                            name ← identifier
                            ws+nl
                            bodies ← pats t n rls (fresh name vm)
                            return (lmap (λ (t , s) → (bind t , s)) bodies)
pats (place x) zero rls vm     = fail
pats (place x) (suc n) rls vm  = constructions n rls vm
pats ⊥ n rls vm = fail

const-parsers : Rules → List (ℕ → TermParser (λ γ → List (Const γ × String)))
const-parsers rs@(trs , ∋rs , _) = lmap (pats ∘′ ∋sub) ∋rs ++ lmap (pats ∘′ tysub) trs

{-# TERMINATING #-}
constructions n rls vm = do
                           cons ← concat <$> all-of (lmap (λ tp → tp n rls vm) (const-parsers rls))
                           inj₁ com ← optional (computation rls vm)
                             where inj₂ _ → return cons
                           s ← get
                           return ((thunk com , s) ∷ cons)


prad : TermParser Compu
prad rules vm = do
                  rest ← get
                  rem_toks ← return ((length ∘′ words) rest )
                  just (tm , str) ← longest <$> constructions rem_toks rules vm
                    where nothing → fail
                  put str
                  wsnl-tolerant (literal ':')
                  rest ← (λ s → just (s , s))
                  rem_toks ← return (length (words rest))
                  just (ty , str) ← longest <$> constructions rem_toks rules vm 
                    where nothing → fail
                  put str
                  left ← (λ s → just (s , ")"))
                  return (tm ∷ ty)

               

pvar : ∀ {γ} → VarMap γ → Parser (Compu γ)
pvar vm = do
            name ← identifier
            just v ← return (lookup name vm)
               where nothing → fail
            return (var v)

{-# TERMINATING #-}
pelim : TermParser Compu
pelim rules vm = do
                   tar ← anyof (bracketed (pelim rules vm) ∷
                               bracketed (prad rules vm) ∷
                               pvar vm ∷ [])
                   ws+nl
                   rest ← (λ s → just (s , s))
                   rem_toks ← return (length (words rest))
                   just (elm , str) ← longest <$> constructions rem_toks rules vm
                     where nothing → fail
                   put str
                   return (elim tar elm)

computation rules vm = anyof (bracketed (prad rules vm) ∷
                              bracketed (pelim rules vm) ∷ pvar vm ∷ [])
-}

construction : ℕ → TermParser Const
computation  : TermParser Compu

open import Pattern using (print-pat)
ppat : Pattern δ → ℕ → TermParser Const
ppat _ zero _ _ = fail
ppat (` x) (suc n)    _ _   = do
                                tok ← token
                                just (at , _) ← return (complete (string x) tok)
                                  where nothing → fail
                                return (` at)
ppat (s ∙ t) n rls vm   = do
                                  l ← ppat s n rls vm    
                                  ws+nl
                                  r ← ppat t n rls vm
                                  return (l ∙ r)
ppat (bind t) (suc n) rls vm  = do
                                  name ← identifier
                                  ws+nl
                                  under ← ppat t n rls (fresh name vm)
                                  return (bind under)
--ppat (place x) zero _ _ = fail                             
ppat (place x) (suc n) rls vm = construction n rls vm
ppat ⊥ _          _   _  = fail


const-parsers : Rules → List (ℕ → TermParser Const)
const-parsers rs@(trs , ∋rs , _) = lmap (ppat ∘′ ∋sub) ∋rs ++ lmap (ppat ∘′ tysub) trs

construction zero _ _ = fail
construction n rules vm = do
                           inj₁ cons ← biggest-consumer (lmap (λ tp → tp n rules vm) (const-parsers rules))
                                    or computation rules vm
                                    where inj₂ comp → return (thunk comp)
                           return cons

open import Data.Nat.Show
prad : TermParser Compu
prad rules vm = do
                  rest ← get
                  rem_toks ← return (length (words rest))
                  tm ← construction rem_toks rules vm
                  wsnl-tolerant (literal ':')
                  rest ← get
                  rem_toks ← return (length (words rest))
                  --put ")"
                  --return (` "remaining: " ∷ ` (show rem_toks))
                  ty ← construction rem_toks rules vm
                  return (tm ∷ ty)

                  

pvar : ∀ {γ} → VarMap γ → Parser (Compu γ)
pvar vm = do
            name ← identifier
            just v ← return (lookup name vm)
               where nothing → fail
            return (var v)

{-# TERMINATING #-}
pelim : TermParser Compu
pelim rules vm = do
                   tar ← anyof (bracketed (pelim rules vm) ∷
                               bracketed (prad rules vm) ∷
                               pvar vm ∷ [])
                   ws+nl
                   rest ← get
                   rem_toks ← return (length (words rest))
                   elm ← construction rem_toks rules vm
                   return (elim tar elm)

computation rules vm = anyof (bracketed (prad rules vm) ∷
                              bracketed (pelim rules vm) ∷ pvar vm ∷ [])
\end{code}

