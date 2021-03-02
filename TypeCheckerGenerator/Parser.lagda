\section{Parsers}

\hide{
\begin{code}
module Parser where
\end{code}
}

\hide{
\begin{code}
open import Data.String using (String; toList; fromList; fromChar; _++_; length)
                        renaming (_==_ to _==ˢ_)
open import Data.Char using (Char; _==_; isDigit; show)
open import Data.Bool using (if_then_else_; Bool; not)
open import Data.Nat using (ℕ; suc; _<ᵇ_)
open import String using (trim←; toNat; trim←')
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_; maybe′)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; foldr)
open import Function using (_∘′_)
open import Category.Monad.State
open import Data.Maybe.Categorical renaming (monad to MaybeMonad)
open import Category.Monad using (RawMonad)
open import Level
module maybemonad = RawMonad {f = 0ℓ} MaybeMonad
\end{code}
}

\hide{
\begin{code}
private
  variable
    A : Set
    B : Set
    C : Set
\end{code}
}

\begin{code}
module Parser where
  Parser' : Set → Set
  Parser' = StateT (List Char) Maybe
  
  Parser : Set → Set
  Parser = StateT String Maybe
 
  →[_]→ : Parser' A → Parser A
  →[ P' ]→  str = do
                    (a , rest) ← (P' ∘′ toList) str
                    just ((a , fromList rest))
                  where open maybemonad

             
  ParserMonad = StateTMonad String MaybeMonad
open Parser
module parsermonad = RawMonad ParserMonad
\end{code}





Useful common parsers:

\begin{code}
module Parsers where

  fail : Parser A
  fail str = nothing

  -- guarantees a parser, if it succeeds, consumes some input
  safe : Parser A → Parser A
  safe p s = do
               (a , s') ← p s
               if length s' <ᵇ length s then just (a , s') else nothing
             where open maybemonad
  
  peak : Parser Char
  peak str with toList str
  ... | []      = nothing
  ... | c ∷ rest = just ((c , fromList (c ∷ rest)))

  all : Parser String
  all = λ s → just (s , "")

  try : Parser A → A → Parser A
  try p a str = p str <∣> just (a , str)

  _or_ : Parser A → Parser B → Parser (A ⊎ B)
  (pa or pb) str = (inj₁ <$> pa) str <∣> (inj₂ <$> pb) str
    where
      open parsermonad

  either_or_ : Parser A → Parser A → Parser A
  (either pa or pb) str = maybe′ just (pb str) (pa str)

  ifp_then_else_ : Parser A → Parser B → Parser B → Parser B
  (ifp p then pthen else pelse) str with p str
  ... | nothing = pelse str
  ... | just x  = pthen str

  nout : Parser ⊤
  nout = return tt
    where open parsermonad

  optional : Parser A → Parser (A ⊎ ⊤)
  optional = _or nout

  complete : Parser A → Parser A
  complete p = do
                 a ← p
                 rest ← all
                 if rest ==ˢ "" then return a else fail
               where open parsermonad

  takeIf' : (Char → Bool) → Parser' Char
  takeIf' p []          = nothing
  takeIf' p (c ∷ chars) = if p c then just (c , chars) else nothing

  takeIf : (Char → Bool) → Parser Char
  takeIf p = →[ takeIf' p ]→

  -- This terminates as we ensure to make p 'safe' before we
  -- use it, forcing the parser to fail if it does not consume
  -- any input
  {-# TERMINATING #-}
  _*[_,_] : Parser A → (A → B → B) → B → Parser B
  p *[ f , b ] = do
                   inj₁ a ← optional (safe p)
                     where inj₂ _ → return b
                   b ← p *[ f , b ] 
                   return (f a b)
    where open parsermonad


  _⁺[_,_] : Parser A → (A → B → B) → B → Parser B
  p ⁺[ f , b ] = pure f ⊛ p ⊛ (p *[ f , b ])
    where open parsermonad

  anyof : List (Parser A) → Parser A
  anyof []       = fail
  anyof (p ∷ ps) = either p or (anyof ps)
\end{code}

\begin{code}
  -- text/number parsing

  whitespace : Parser ⊤
  whitespace str = just (tt , trim← str)

  ws+nl : Parser ⊤
  ws+nl str = just (tt , trim←' str)

  ws+nl! : Parser ⊤
  ws+nl! = do
              c ← takeIf Data.Char.isSpace
              ws+nl
             where open parsermonad

  ws-tolerant : Parser A → Parser A
  ws-tolerant p = do
                    whitespace
                    r ← p
                    whitespace
                    return r
    where open parsermonad

  wsnl-tolerant : Parser A → Parser A
  wsnl-tolerant p = do
                      ws+nl
                      r ← p
                      ws+nl
                      return r
    where open parsermonad

  wsnl-tolerant! : Parser A → Parser A
  wsnl-tolerant! p = do
                      ws+nl!
                      r ← p
                      ws+nl!
                      return r
    where open parsermonad

  literal' : Char → Parser' Char
  literal' c [] = nothing
  literal' c (x ∷ rest)
    = if c == x then just (c , rest)
                else nothing
  
  literal : Char → Parser Char
  literal c = →[ literal' c ]→

  newline = literal '\n'

  nextChar' : Parser' Char
  nextChar' []          = nothing
  nextChar' (c ∷ chars) = just (c , chars)

  nextChar = →[ nextChar' ]→

  literalAsString = (fromChar <$>_) ∘′ literal
    where open parsermonad

  string : String → Parser String
  string str = foldr
                   (λ c p → (pure _++_) ⊛ (literalAsString c) ⊛ p)
                   (return "") (toList str)
    where open parsermonad

    
  stringof : (Char → Bool) → Parser String
  stringof p = takeIf p *[ _++_ ∘′ fromChar , "" ]

  until : (Char → Bool) → Parser String
  until p = stringof (not ∘′ p)

  nonempty : Parser String → Parser String
  nonempty p = do
                 r ← p
                 if r ==ˢ "" then (λ _ → nothing) else return r
    where open parsermonad

  nat : Parser ℕ
  nat = do
          d ← nonempty (stringof isDigit)
          return (toNat d)
        where open parsermonad

  
  bracketed : Parser A → Parser A
  bracketed p = do
                  literal '('
                  a ← ws-tolerant p
                  literal ')'
                  return a
     where open parsermonad

  curlybracketed : Parser A → Parser A
  curlybracketed p = do
                  literal '{'
                  a ← ws-tolerant p
                  literal '}'
                  return a
    where open parsermonad

  squarebracketed : Parser A → Parser A
  squarebracketed p = do
                  literal '['
                  a ← ws-tolerant p
                  literal ']'
                  return a
    where open parsermonad
open Parsers
\end{code}
