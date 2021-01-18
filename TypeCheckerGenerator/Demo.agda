module Demo where

import Test.Specs.STLC as STLC
open STLC using (rules)
open STLC.combinators

open import TypeChecker using (infer; check)
open import CoreLanguage
open import Data.Nat using (suc)
open import Failable
open import Thinning using (ε; _-,_)
open import Data.String
open import Context using (Context)







-- now we can do some examples


term : Term lib compu 0
term = lam (~ ze) ∷ (α ⇨ α)

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
         ((lam (thunk (elim (ess (var ze)) (ess (` 'a'))))) ∷ ((α ⇨ α) ⇨ α))
         (thunk (elim (ess (bind (thunk (var ze))) ∷ ((α ⇨ α) ⇨ (α ⇨ α))) (ess (bind (thunk (var ze))))))
-}

{-
term = ess (bind (thunk (elim (ess (var (su (su ze)))) (ess (` 'a'))))) ∷ (β ⇨ α)
ctx = ε -, (α ⇨ α) -, β
-}
