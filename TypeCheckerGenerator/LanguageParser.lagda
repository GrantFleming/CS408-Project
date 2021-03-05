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
Rules = List TypeRule × List ∋rule

TermParser : Scoped → Set
TermParser A = ∀ {γ} → VarMap γ → Parser (A γ)

\end{code}


\begin{code}
-- first we get all the patterns that define constructions

patterns : Rules → List (Pattern 0)
patterns (trs , ∋rs) = lmap tysub trs ++ lmap ∋sub ∋rs

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
  pre-tail-pats = filtered (proj₁ pats)
  tail-pats = (tail ∘′ proj₁) pats

  phead : TermParser Const
  ptail : TermParser Const
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
                                             h ← ppat p vm
                                             ws+nl
                                             ` "" ← ptail vm
                                               where t → return (h ∙ t)
                                             return h)
                                             head-pats)

  ptail vm = either biggest-consumer (lmap (λ p → ppat p vm) tail-pats) or return (` "")



  
  construction vm = either potentially-bracketed (phead vm)
                        or do
                             com ← computation vm
                             return (thunk com)


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
