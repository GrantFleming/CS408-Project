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
open import Data.List hiding (lookup; map; fromMaybe)
open import Data.Product using (_×_; Σ-syntax; _,_; Σ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Char hiding (_≟_)
open import Data.String using (String)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Nat using (suc; ∣_-_∣)
open import Data.Bool using (Bool; _∧_; _∨_; not; if_then_else_)
open import Function using (_∘′_)
open import Thinning using (_⊑_)
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
    δ : Scope
    γ : Scope
    γ' : Scope
\end{code}
}

We define mappings for variable names to svars, and create a type for pattern
parsers which aim to parse some pattern along with mappings from names to
svars in the pattern. This map is used to retrieve the svars when parsing
components such as expressions which depend on this.

\begin{code}
SVar : Pattern γ → Set
SVar p = Σ[ δ ∈ Scope ] svar p δ 

SVarMap : Pattern γ → Set
SVarMap p = Map (SVar p)

PatternParser : Scope → Set
PatternParser γ = Parser (Σ[ p ∈ Pattern γ ] SVarMap p)
\end{code}

\begin{code}
module PatternParser where
  open parsermonad
  
  forbidden-atom-chars : List Char
  forbidden-atom-chars = '(' ∷ ')' ∷ '{' ∷ '}' ∷ '.' ∷ ':' ∷ ',' ∷ []
  
  atomchar : Char → Bool
  atomchar c = isLower c ∨ ( not (isAlpha c) ∧ not (isSpace c) ∧ not (any (c ==_) forbidden-atom-chars))
  
  idchar : Char → Bool
  idchar c = isAlpha c ∧ (not (isLower c))

      
  identifier : Parser String
  identifier = nonempty (stringof idchar)  
  
  binding : Parser String
  binding = do
              name ← identifier
              literal '.'
              return name

\end{code}
  
\begin{code}
  pat : PatternParser γ
  private
    atom : PatternParser γ
    atom = (_, empty) <$> (` <$> nonempty (stringof atomchar))     
    
    plc : PatternParser γ
    plc {γ} = do
                name ← identifier
                ifp literal '.' then fail
                                else return ((place ι) , singleton name (γ , ⋆))

    {-# TERMINATING #-}
    binder : PatternParser γ
    binder {γ} = do
                   name ← safe binding
                   whitespace
                   (subterm , vmap) ← pat {suc γ}
                   return ((bind subterm) , map (λ {(δ , st) → (δ , bind st)  }) vmap)
    
  pat {γ} = do
              (fst , vmap) ← anyof(atom {γ} ∷ plc ∷ binder ∷ bracketed pat ∷ [])              
              inj₁ (snd , vmap') ← optional (do
                                               whitespace
                                               pat {γ})
                where inj₂ _ → return (fst , vmap)
              return ((fst ∙ snd) , union (map (λ { (δ , st) → (δ , (st ∙))}) vmap)
                                          (map (λ { (δ , st) → (δ , (∙ st))}) vmap'))

  closed-pattern = pat {0}
open PatternParser
\end{code}

Now we must parse expressions. The parsing of an expression must be done in
terms of a pattern, but also a mapping from variable names to svars, thus the
user does not have to deal with the svars externally.

\begin{code}
{-
  If we want to refer to variables by name in our expressions, then we have to
  use another map

  Also, tidy up these types ya animal
-}

module ExpressionParser where
  open import Expression
  open import Data.Maybe using (maybe′)
  open import Data.Nat using (zero; _≟_)
  open import Relation.Nullary using (yes; no)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Substitution using (_⇒[_]_)
  open import BwdVec using (ε; _-,_)
  open parsermonad

  VarMap : Scoped
  VarMap γ = Map (Var γ)

  private
    variable
      δ' : Scope
      p : Pattern δ

  ConstParser = ∀ {δ} → (p : Pattern δ) → (γ : Scope) → VarMap γ → SVarMap p → Parser (Expr p const γ)
  CompuParser = ∀ {δ} → (p : Pattern δ) → (γ : Scope) → VarMap γ → SVarMap p → Parser (Expr p compu γ)
    
  econst : ConstParser
  ecompu : CompuParser

  private
    eatom : ConstParser
    eatom _ _ _ _ = ` <$> nonempty (stringof atomchar) 
    
    {-# TERMINATING #-}
    ebinder : ConstParser
    ebinder p γ vmap svmap = do
                         name ← safe binding
                         whitespace
                         subexpr ← econst p (suc γ) (insert name ze (map su vmap)) svmap
                         return (bind subexpr)
    
    ethunk : ConstParser
    ethunk p γ vmap svmap = do
                        comp ← curlybracketed (ecompu p γ vmap svmap)
                        return (thunk comp)
    
    esvar : (p : Pattern γ) → SVarMap p → Parser (SVar p)
    esvar p svmap = do
                        name ← identifier
                        ifp literal '.' then fail
                                        else maybe′ return fail (lookup name svmap)

    eσ : (δ γ : Scope) → (p : Pattern δ') → VarMap γ → SVarMap p → Parser (δ ⇒[ Expr p compu ] γ)
    eσ zero γ p vmap svmap    = return ε
    eσ (suc δ) γ p vmap svmap = do
                                  rest ← eσ δ γ p vmap svmap
                                  ws-tolerant (literal ',')
                                  this ← ecompu p γ vmap svmap
                                  return (rest -, this)

    einst : ConstParser
    einst p γ vmap svmap = do
                             (δ , ξ) ← esvar p svmap                             
                             σ ← eσ δ γ p vmap svmap
                             return (ξ / σ)
                             
    evar : CompuParser
    evar p γ vmap svmap = do
                            literal '.'
                            name ← identifier
                            maybe′ (return ∘′ var) fail (lookup name vmap)
    
    erad : CompuParser
    erad p γ vmap svmap = do
                            --return (` "lol" ∷ ` "LOL") 
                            t ← econst p γ vmap svmap
                            ws-tolerant (literal ':')
                            T ← econst p γ vmap svmap
                            return (t ∷ T)
    
  econst p γ vmap svmap = do
             fst ← anyof (eatom   p γ vmap svmap  ∷
                          ebinder p γ vmap svmap  ∷
                          ethunk  p γ vmap svmap  ∷
                          einst   p γ vmap svmap  ∷
                          bracketed (econst p γ vmap svmap) ∷ [])
             inj₁ snd ← optional (do
                                  whitespace
                                  econst p γ vmap svmap)
               where inj₂ _ → return fst
             return (fst ∙ snd)

  ecompu p γ vmap svmap = do
             fst ← anyof (evar p γ vmap svmap ∷
                          erad p γ vmap svmap ∷
                          bracketed (ecompu p γ vmap svmap) ∷ [])
             inj₁ eliminator ← optional (do
                                           whitespace
                                           econst p γ vmap svmap)
                  where inj₂ _ → return fst                  
             return (elim fst eliminator)
open ExpressionParser
\end{code}

