module Demo where

open import STLC using (rules)
open import TypeChecker using (infer; check)
open import CoreLanguage
open import Data.Nat using (suc)
open import Failable
open import Thinning using (ε)
open import Data.String


-- producing terms in the internal language is tedious and error prone
-- so to save a little headache we will use some combinators

α : ∀{γ} → Term lib const γ
α = ess (` 'α')

a : ∀{γ} → Term lib const γ
a = ess (` 'a')

b : ∀{γ} → Term lib const γ
b = ess (` 'b')

_⇨_ : ∀{γ} → Lib-Const γ → Lib-Const γ → Term lib const γ
x ⇨ y = ess (x ∙ ess (ess (` '→') ∙ y))
infixr 20 _⇨_

lam : ∀ {γ} → Term lib const (suc γ) → Term lib const γ
lam t = ess (bind t)

~ : ∀ {γ} → Var γ → Term lib const γ
~ vr = thunk (var vr)

app : ∀ {γ} → Lib-Compu γ → Lib-Const γ → Term lib compu γ
app e s = ess (elim e s)















-- now we can do some examples

term : Term lib compu 0
term = {!!}

test : String
test with infer rules ε term
... | succeed x = print x
... | fail    x = x












-- lam (~ ze) ∷ (α ⇨ α)

{- 
app
      (lam (~ ze) ∷ (α ⇨ α))
      a  
-}

{- 
app
      (lam (~ ze) ∷ ((α ⇨ α) ⇨ (α ⇨ α)))
      (lam (~ ze))
-}

{-
AFTER ADDING b as a value

app
         ((lam b) ∷ (α ⇨ α))
         a

-}

