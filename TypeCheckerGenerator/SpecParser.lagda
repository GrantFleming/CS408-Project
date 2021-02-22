\section{}

\hide{
\begin{code}
module SpecParser where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Pattern hiding (map)
open import Thinning using (ι)
open import Category.Monad using (RawMonad)
open import Data.List hiding (lookup; map)
open import Data.Product using (_×_; Σ-syntax; _,_; Σ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Char
open import Data.String using (String)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Nat using (suc; ∣_-_∣)
open import Data.Bool using (Bool; _∧_; _∨_; not)
import Data.Tree.AVL.Map as MapMod
open MapMod <-strictTotalOrder-≈
open import Parser as P
open P.Parser
open P.Parsers
\end{code}
}

\hide{
\begin{code}
private
  variable
    γ : Scope
    p : Pattern 0
\end{code}
}

We define mappings for variable names to svars, and create a type for pattern
parsers which aim to parse some pattern along with mappings from names to
svars in the pattern. This map is used to retrieve the svars when parsing
components such as expressions which depend on this.

\begin{code}
SVar : Pattern γ → Set
SVar p = Σ[ δ ∈ Scope ] svar p δ 

VarMap : Pattern γ → Set
VarMap p = Map (SVar p)

PatternParser : Scope → Set
PatternParser γ = Parser (Σ[ p ∈ Pattern γ ] VarMap p)
\end{code}

\begin{code}
module PatternParser where
  open parsermonad
  
  forbidden-atom-chars : List Char
  forbidden-atom-chars = '(' ∷ ')' ∷ '{' ∷ '}' ∷ []
  
  atomchar : Char → Bool
  atomchar c = isLower c ∨ ( not (isAlpha c) ∧ not (isSpace c) ∧ not (any (c ==_) forbidden-atom-chars))
  
  idchar : Char → Bool
  idchar c = isAlpha c ∧ (not (isLower c))
\end{code}
  
\begin{code}
  pat : PatternParser γ
  
  atom : PatternParser γ
  atom = (_, empty) <$> (` <$> nonempty (stringof atomchar)) 
    
  identifier : Parser String
  identifier = nonempty (stringof idchar)  

  binding : Parser String
  binding = do
              name ← identifier
              literal '.'
              return name
 

  plc : PatternParser γ
  plc {γ} = do
              name ← identifier
              ifp literal '.' then fail
                              else return ((place ι) , (singleton name (γ , ⋆)))

  {-# TERMINATING #-}
  binder : PatternParser γ
  binder {γ} = do
                 name ← safe binding
                 whitespace
                 (subterm , vmap) ← pat {suc γ}
                 return ((bind subterm) , map (λ {(δ , st) → (δ , bind st)  }) vmap)
  
  pat {γ} = do
              (fst , vmap) ← anyof(atom {γ} ∷ plc ∷ binder ∷ bracketed pat ∷ [])              
              inj₁ (snd , vmap') ← optional (whitespace >>= λ _ → pat {γ})
                where inj₂ _ → return (fst , vmap)
              return ((fst ∙ snd) , union (map (λ { (δ , st) → (δ , (st ∙))}) vmap)
                                          (map (λ { (δ , st) → (δ , (∙ st))}) vmap'))

  closed-pattern = pat {0}
open PatternParser
\end{code}

