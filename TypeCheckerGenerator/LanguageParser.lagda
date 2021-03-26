\section{Parsing the language}
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
open import Data.List using (List; _∷_; []; any; _++_; length; concat; partition) renaming (map to lmap; foldr to lfoldr)
open import Data.Nat using (ℕ; suc; zero; _<ᵇ_; ∣_-_∣; _≡ᵇ_) renaming (_+_ to  _+'_)
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
We now want the user to be able to supply a candidate for type checking by
writing the term in a file as opposed to supplying it as an Agda code
representation in our internal syntax and so we build a second parser for this
purpose.

We use the patterns in our type rules and ∋ rules to determine valid
constructions in the language and then use these patterns to guide our parsing,
however, we must first overcome one major problem.

A user is perfectly able to have some \emph{place} as the first part of a pattern.
Attempting to parse this in a top-down manner may lead to infinite recursion in
the same way that parsing a left-recursive grammar might. We can solve this problem
in two ways, we could either implement a more sophisticated parser that is tolerant
of such grammars or we could pre-process the patterns to create a right-recursive
equivalent. We opt for the latter option due to time constraints.

Since our objective is to synthesize some type, the top-level parsable element here
is a single \emph{computation}.
\hide{
\begin{code}
private
  variable
    δ : Scope
    γ : Scope
    A : Set
\end{code}

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
TermParser A = ∀ {γ} → VarMap γ → Parser (A γ)

TailParser : Set
TailParser = ∀ {γ} → Const γ → VarMap γ → Parser (Const γ)
\end{code}


\begin{code}
-- first we get all the patterns that define constructions

patterns : Rules → List (Pattern 0)
patterns (trs , ∋rs , ers) = lmap tysub trs ++ lmap ∋sub ∋rs ++ lmap eliminator ers

{- 
But now we may have to deal with the left recursion problem! So lets
sort that.
-}

-- we need to know if a pattern begins with a place (as it would be
-- left recursive)

open import Relation.Unary using (Decidable)
open import Relation.Nullary using (yes; no)
open import Thinning using (_⊑_; ι)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Pattern using (_/≟_)
open import Data.List using (filter)

data LeftRecursive (γ : Scope) : Pattern γ → Set where
  pl : ∀ {i : δ ⊑ γ} → LeftRecursive γ (place i)
  l∙ : ∀ {i : δ ⊑ γ} → (r : Pattern γ) → LeftRecursive γ (place i ∙ r)

left-recursive : Decidable (LeftRecursive γ)
left-recursive (` x)           = no (λ {()})
left-recursive (` x ∙ r)       = no (λ {()})
left-recursive ((l ∙ l₁) ∙ r)  = no (λ {()})
left-recursive (bind l ∙ r)    = no (λ {()})
left-recursive (place x ∙ r)   = yes (l∙ r)
left-recursive (⊥ ∙ r)         = no λ {()}
left-recursive (bind x)        = no λ {()}
left-recursive (place x)       = yes pl
left-recursive ⊥               = no (λ {()})

split : List (Pattern 0) → (List (Pattern 0) × List (Pattern 0))
split pats = partition left-recursive pats

-- the old left recursive stuff made safe
tail : List (Pattern 0) → List (Pattern 0)
tail lrcr = (lmap (λ where
                       ((place x) ∙ r) → r
                       p               → p)
                   (filter ((place ι) /≟_) lrcr))

filtered : List (Pattern 0) → List (Pattern 0)
filtered ls = filter ((place ι) /≟_) ls

module LParsers (rules : Rules) where

  pats = (split ∘′ patterns) rules

  head-pats = proj₂ pats
  tail-pats = (tail ∘′ proj₁) pats

  phead : TermParser Const
  ptail : ℕ → TailParser
  computation : TermParser Compu
  construction : TermParser Const

  ppat : Pattern γ → TermParser Const
  ppat (` x) vm   = do
                      tok ← token
                      just (at , _) ← return (complete (string x) tok)
                        where nothing → fail
                      return (` at)
  ppat (l ∙ r) vm = do
                      left ← ppat l vm
                      ws+nl
                      right ← ppat r vm
                      return (left ∙ right)
  ppat (bind p) vm = do
                       tok ← token
                       just (name , _) ← return (complete identifier tok)
                         where nothing → fail
                       ws+nl
                       under ← ppat p (fresh name vm)
                       return (bind under)
  ppat (place x) = construction
  ppat ⊥ vm = fail

  {-# TERMINATING #-}
  phead vm = biggest-consumer (lmap (λ p → do
                                             (n , _) ← how-many? (wsnl-tolerant (literal '('))
                                             h ←  ppat p vm
                                             (m , _) ←  wsnl-tolerant (max n how-many? (wsnl-tolerant (literal ')')))
                                             if n <ᵇ m then fail else return get
                                             ptail ∣ n - m ∣ h vm)
                                             head-pats)


  ptail n tm vm = either biggest-consumer (lmap (λ p → (do
                                                       start ← ppat p vm
                                                       (closed , _) ← max n how-many? (wsnl-tolerant (literal ')'))
                                                       if n <ᵇ closed then fail
                                                                      else return get
                                                       if closed ≡ᵇ 0
                                                         then (do
                                                                tl ← ptail n start vm
                                                                return (tm ∙ tl))
                                                         else ptail ∣ n - closed ∣ (tm ∙ start) vm
                                                       )) tail-pats)
                   or (do
                          exactly n (wsnl-tolerant (literal ')'))
                          return tm)



  
  construction vm = either (phead vm)
                        or (do
                             com ← computation vm
                             ws+nl
                             inj₁ tm ← optional (ptail 0 (thunk com) vm)
                               where inj₂ _ → return (thunk com)
                             return tm)


  prad : TermParser Compu
  prad vm = do
              t ← construction vm
              wsnl-tolerant (literal ':')
              T ← construction vm
              return (t ∷ T)

  pvar : TermParser Compu
  pvar vm = do
              tok ← token
              just (name , _) ← return (complete identifier tok)
                where nothing → fail
              just v ← return (lookup name vm)
                where nothing → fail
              return (var v)

  pelim : TermParser Compu
  pelim vm = do
               tar ← computation vm
               ws+nl
               e ← construction vm
               return (elim tar e)
  {-# TERMINATING #-}
  computation vm = biggest-consumer (bracketed (prad vm) ∷
                                     bracketed (pelim vm) ∷
                                     pvar vm ∷
                                     [])
\end{code}
}
\section{Putting it all together}
We now have all the required components for our type-checker. A user runs the software
with the command \begin{verbatim}TypeCheck <spec-file> <term-file>\end{verbatim}We
first read the whole of the spec-file as a string, and parse the rules from it with
our DSL parser. Armed with the set of rules we can then parse a term in the language
from the term-file, and then attempt to type the term with a simple call to 'infer'.

