\section{Parser combinators}

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
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; ∣_-_∣)
open import String using (trim←; toNat; trim←')
open import Data.Product using (Σ-syntax; _,_; _×_)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_; maybe′)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; foldr; map)
open import Data.Vec using (Vec; _∷_; [])
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

We acknowledge that parsing is an entire field of study in its own right
and that it is certainly not the focus of this project. However,
to have the user describe the type system in our DSL rather than in Agda
code, we will require a parser to make sense of this input.

We capitalise on the definitions in the Agda standard library and define
a parser in terms of the State monad transformer. A parser is given a string
as input, then it may fail or it may succeed and return something along with
the rest of the string minus what was consumed during parsing. For convenience,
we also provide a similar type that describes a parser operating on lists of
characters and a way to plumb this into a 'real' parser by making the
appropriate conversions.

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
\end{code}

\hide{
\begin{code}
  ParserState : RawMonadState String Parser
  ParserState = StateTMonadState String MaybeMonad
  ParserMonad = monad
    where open RawMonadState ParserState
open Parser
module parsermonad = RawMonad ParserMonad
module parserstatemonad = RawMonadState ParserState
\end{code}
}

We build a small library of useful parsers, allowing us to build parsers
incrementally using these parser combinators. We provide parsers that parser
conditionally, parse zero-or-more times. Parsers that fail if they do not
consume all their input, parsers to parse literal characters and strings. The
list is somewhat large so we will not detail these parsers here. A full list of
the basic combinators used is available in appendix \ref{appendix-parsercombinators}.
\hide{
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

  consumes : Parser A → Parser (ℕ × A)
  consumes p = do
                 bfr ← (λ s → just (length s , s))
                 a ← p
                 afr ← (λ s → just (length s , s))
                 return (∣ bfr - afr ∣ , a)
               where open parsermonad

  biggest-of_and_ : Parser A → Parser A → Parser A
  biggest-of_and_ p1 p2 str with p1 str | p2 str
  ... | nothing | nothing = nothing
  ... | nothing | just p = just p
  ... | just p | nothing = just p
  ... | just (a1 , rst1) | just (a2 , rst2) = just (if length rst1 <ᵇ length rst2 then (a1 , rst1) else (a2 , rst2))

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

  biggest-consumer : List (Parser A) → Parser A
  biggest-consumer [] = fail
  biggest-consumer (p ∷ ps) = biggest-of p and biggest-consumer ps

  all-of : List (Parser A) → Parser (List A)
  all-of [] str = just ([] , str)
  all-of ps str = just (foldr (λ p las → maybe′ (λ (a , _) → a ∷ las) las (p str) ) [] ps , "")

  {-# TERMINATING #-}
  how-many? : Parser A → Parser (Σ[ n ∈ ℕ ] Vec A n)
  how-many? p = ifp p then (do
                              a ←  safe p
                              (n , as) ← how-many? p
                              return (ℕ.suc n , a ∷ as))
                else return (0 , [])
    where open parsermonad

  max_how-many? : ℕ → Parser A → Parser (Σ[ n ∈ ℕ ] Vec A n)
  max zero how-many? _    = return (0 , [])
    where open parsermonad
  max (suc n) how-many? p = ifp p then (do
                              a ←  safe p
                              (n , as) ← max n how-many? p
                              return (ℕ.suc n , a ∷ as))
                else return (0 , [])
    where open parsermonad

  exactly : (n : ℕ) → Parser A → Parser (Vec A n)
  exactly zero _  = return []
    where open parsermonad
  exactly (suc n) p = do
                        a ← p
                        as ← exactly n p
                        return (a ∷ as)
    where open parsermonad
  
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
                  a ← wsnl-tolerant p
                  literal ')'
                  return a
     where open parsermonad

  potentially-bracketed : Parser A → Parser A
  potentially-bracketed p = either bracketed p or p

  curlybracketed : Parser A → Parser A
  curlybracketed p = do
                  literal '{'
                  a ← wsnl-tolerant p
                  literal '}'
                  return a
    where open parsermonad

  squarebracketed : Parser A → Parser A
  squarebracketed p = do
                  literal '['
                  a ← wsnl-tolerant p
                  literal ']'
                  return a
    where open parsermonad
open Parsers
\end{code}
}
