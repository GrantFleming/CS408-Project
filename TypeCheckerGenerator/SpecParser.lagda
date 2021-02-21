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
open import Data.List
open import Data.Char
open import Data.String using (String)
open import Data.Nat using (suc)
open import Data.Bool using (Bool; _∧_; _∨_; not)
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
\end{code}
}

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
  pat : Parser (Pattern γ)
  
  atom : Parser (Pattern γ)
  atom = pure ` ⊛ nonempty (stringof atomchar)
    
  identifier : Parser String
  identifier = nonempty (stringof idchar)  
  
  binding : Parser String
  binding = do
              name ← identifier
              literal '.'
              return name
  
  
  plc : Parser (Pattern γ)
  plc = do
          name ← identifier
          ifp literal '.' then fail
                          else return (place ι)
  
  -- TO DO - collect names and compute svars!
  {-# TERMINATING #-}
  binder : Parser (Pattern γ)
  binder {γ} = do
                 name ← safe binding
                 whitespace
                 subterm ← pat {suc γ}
                 return (bind subterm)
  
  pair : Parser (Pattern γ)
  pair = do
          left ← anyof (atom ∷ plc ∷ binder ∷ bracketed pat ∷ [])
          whitespace
          right ← pat
          return (left ∙ right)
  
  pat = anyof (pair ∷ atom ∷ plc ∷ binder ∷ bracketed pat ∷ [])
open PatternParser

\end{code}
