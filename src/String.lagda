\begin{code}
module String where
\end{code}

\begin{code}
open import Data.String using (String; toList; fromList)
open import Data.Nat using (ℕ; _+_; _*_; _<ᵇ_; ∣_-_∣)
open import Data.Char using (Char; isSpace; toℕ; _==_)
open import Data.List using (List; _∷_; []; reverse; map; foldr; dropWhile)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_; not)
open import Function using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}

\begin{code}
isSpace' : Char → Bool
isSpace' c = isSpace c ∧ not (c == '\n')

trimℓ← : List Char → List Char
trimℓ← [] = []
trimℓ← (c ∷ chars) with isSpace' c
... | false = c ∷ chars
... | true  = trimℓ← chars

trim← : String → String
trim← = fromList ∘′ trimℓ← ∘′ toList

trimℓ←' : List Char → List Char
trimℓ←' [] = []
trimℓ←' (c ∷ chars) with isSpace c
... | false = c ∷ chars
... | true  = trimℓ←' chars

trim←' : String → String
trim←' = fromList ∘′ trimℓ←' ∘′ toList

toDigit : Char → ℕ
toDigit c with toℕ c
... | num = if (47 <ᵇ num) ∧ (num <ᵇ 58)
               then ∣ num - 48 ∣
               else 0

toNat : String → ℕ
toNat = helper ∘′ (map toDigit) ∘′ reverse ∘′ toList
  where
    helper : List ℕ → ℕ
    helper = foldr (λ d r → d + (10 * r)) 0
\end{code}
