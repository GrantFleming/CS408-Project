module Demo where

import Test.Specs.STLC as STLC
open STLC using (rules)
open STLC.combinators

open import TypeChecker using (infer; check)
open import CoreLanguage
open import Data.Nat using (suc)
open import Failable
open import BwdVec
open import Data.String
open import Context using (Context)







-- now we can do some examples


term : Term compu 0
term = {!!}

ctx : Context 0
ctx = ε

test : String
test with infer rules ctx term
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
         ((lam b) ∷ (α ⇨ β))
         a

-}

{-
(λx.xa ∷ ((α→α)→α))  ((λx.x ∷ ((α→α)→(α→α)))  (λx.x))

app
         ((lam (thunk (app (var ze) a))) ∷ ((α ⇨ α) ⇨ α))
         (thunk (app (bind (thunk (var ze)) ∷ ((α ⇨ α) ⇨ (α ⇨ α))) (bind (thunk (var ze)))))
-}

{-
term = (bind (thunk (app (var (su (su ze))) a))) ∷ (β ⇨ α)
ctx = ε -, (α ⇨ α) -, β
-}
