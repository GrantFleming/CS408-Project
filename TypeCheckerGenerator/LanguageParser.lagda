\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module LanguageParser where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Pattern using (Pattern; `; _∙_; bind; place; _⊗_)
open import Data.String using (String) renaming (_++_ to _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Char using (Char; isAlpha; isDigit; isSpace; _==_)
open import Data.List using (List; _∷_; []; any; _++_) renaming (map to lmap)
open import Data.Bool using (Bool; _∨_; not; _∧_)
open import Data.Nat using (suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘′_)
open import Parser
open Parser.Parser
open Parser.Parsers
open parsermonad hiding (_⊗_)
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

\begin{code}

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

construction : TermParser Const
computation  : TermParser Compu


ppat : Pattern δ → TermParser Const
ppat (` x)    _ _   = do
                           tok ← token
                           just (at , _) ← return (complete (string x) tok)
                             where nothing → fail
                           return (` at)
ppat (s ∙ t) rls vm   = do
                           l ← ppat s rls vm
                           ws+nl
                           r ← ppat t rls vm
                           return (l ∙ r)
ppat (bind t) rls vm  = do
                           name ← identifier
                           ws+nl
                           under ← ppat t rls (fresh name vm)
                           return (bind under)
ppat (place x) rls vm = construction rls vm


const-parsers : Rules → List (TermParser Const)
const-parsers rs@(trs , ∋rs , _) = lmap (ppat ∘′ ∋sub) ∋rs ++ lmap (ppat ∘′ tysub) trs


construction rules vm = do
                           inj₁ cons ← anyof (lmap (λ tp → tp rules vm) (const-parsers rules))
                                    or computation rules vm
                                    where inj₂ comp → return (thunk comp)
                           return cons

prad : TermParser Compu
prad rules vm = do
                  tm ← construction rules vm
                  wsnl-tolerant (literal ':')
                  ty ← construction rules vm
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
                   elm ← construction rules vm
                   return (elim tar elm)

computation rules vm = anyof (bracketed (prad rules vm) ∷
                              bracketed (pelim rules vm) ∷ pvar vm ∷ [])
\end{code}

