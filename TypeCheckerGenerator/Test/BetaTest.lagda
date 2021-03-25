\hide{
\begin{code}
module Test.BetaTest where

open import CoreLanguage
open import Semantics
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Failable hiding (_>>=_)
open import Test.Specs.STLC using (rules; betarules; etarules)
open Test.Specs.STLC.combinators

private
  variable
    γ : Scope

open β-rule
\end{code}
}
\begin{code}
------------------------------------------------------
-- β-reduction tests
------------------------------------------------------

module βredtests where

  open import TypeChecker using (check-premise-chain)
  open import BwdVec using (ε)
  PC = check-premise-chain rules ε

  test1 : Failable (Compu 0)
  test1 = reduce betarules PC (lam (~ ze)) (α ⇨ α) a
  
  _ : test1 ≡ succeed (a ∷ α)
  _ = refl
  
  -- function as input
  test2 : Failable (Compu 0)
  test2 = reduce betarules PC (lam (~ ze)) ((α ⇨ α) ⇨ (α ⇨ α)) (lam (~ ze))
  
  _ : test2 ≡ succeed (lam (~ ze) ∷ (α ⇨ α))
  _ = refl
  
  -- take in a function, an argument and apply them
  func : Const γ
  func = lam (lam (thunk (app (var (su ze)) (~ ze))))
  
  ftype : Const γ
  ftype = (α ⇨ α) ⇨ α ⇨ α
  
  arg1  : Const γ
  arg1 = lam (~ ze)
  
  reducable-term : Compu 1
  reducable-term = elim (elim (func ∷ ftype) arg1) (thunk (var ze))
  
  test3 : Failable (Compu 0)
  test3 = reduce betarules PC func ftype arg1
  
  _ : test3 ≡ succeed (lam (thunk (app (arg1 ∷ (α ⇨ α)) (~ ze))) ∷ (α ⇨ α))
  _ = refl

-------------------------------------------------
-- Normalization by evaluation tests
-------------------------------------------------

module normbyeval where

  open import TypeChecker using (infer; check-premise-chain)
  open import Data.Product using (_,_)
  open import BwdVec
  PC = check-premise-chain rules

  -- take in a function, an argument and apply them
  func : Const γ
  func = lam (lam (thunk (app (var (su ze)) (~ ze))))
  
  ftype : Const γ
  ftype = (α ⇨ α) ⇨ α ⇨ α
  
  arg1  : Const γ
  arg1 = lam (~ ze)
  
  reducable-term : Compu 1
  reducable-term = elim (elim (func ∷ ftype) arg1) (thunk (var ze))


  -- should perform a single reduction

  test1 : Const 0
  test1 = normalize etarules betarules ((infer rules) , PC) ε α (thunk (app (lam (~ ze) ∷ (α ⇨ α)) a))

  _ : test1 ≡ a
  _ = refl

  -- should reduce multiple nested eliminations

  test2 : Const 1
  test2 = normalize etarules betarules
          ((infer rules) , PC) (ε -, α) α reducable-term
  
  _ : test2 ≡ thunk (var ze)
  _ = refl

  -- should eta-long variable

  test3 : Const 1
  test3 = normalize etarules betarules
          ((infer rules) , PC) (ε -, (α ⇨ α)) (α ⇨ α) (var ze)

  _ : test3 ≡ lam (thunk (app (var (su ze)) (~ ze)))
  _ = refl

  -- should eta-long stuck eliminations with function type

  test4 : Const 1
  test4 = normalize etarules betarules ((infer rules) , PC)
          (ε -, (α ⇨ (α ⇨ α))) (α ⇨ α) (app (var ze) a)

  _ : test4 ≡ lam (thunk (app (app (var (su ze)) a) (~ ze)))
  _ = refl

    -- should normalize under a binder

  test5 : Const 0
  test5 = normalize etarules betarules
          ((infer rules) , PC) ε α (lam (thunk (app (lam (~ ze) ∷ (α ⇨ α)) a)))

  _ : test5 ≡ lam a
  _ = refl

  -- should normalize the eliminator, even if the target is neutral

  test6 : Const 1
  test6 = normalize etarules betarules
          ((infer rules) , PC) (ε -, (α ⇨ α)) α (app (var ze)
          (thunk (app (lam (~ ze) ∷ (α ⇨ α)) a)))

  _ : test6 ≡ thunk (app (var ze) a)
  _ = refl

  -- should normalize the target even if it results in a neutral term

  test7 : Const 1
  test7 = normalize etarules betarules
          ((infer rules) , PC) (ε -, α) α
          (app (app (lam (~ (su ze)) ∷ (α ⇨ α)) a) a)

  _ : test7 ≡ thunk (app (var ze) a)
  _ = refl

  -- should normalize even if the elimination target body was initially stuck
  test8 : Const 0
  test8 = normalize etarules betarules
          ((infer rules) , PC) ε α
          (app (lam (thunk (app (var ze) a)) ∷ ((α ⇨ α) ⇨ α))
          (lam (~ ze)))

  _ : test8 ≡ a
  _ = refl

  -- should eta-expand multiple times
  test9 : Const 1
  test9 = normalize etarules betarules
          ((infer rules) , PC) (ε -, (α ⇨ α ⇨ α)) (α ⇨ α ⇨ α) (var ze)

  _ : test9 ≡ lam (lam (thunk (app (app (var (su (su ze))) (~ (su ze))) (~ ze))))
  _ = refl

\end{code}
