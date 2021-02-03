module Test.BetaTest where

open import CoreLanguage
open import Semantics
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Failable hiding (_>>=_)
open import Test.Specs.STLC using (rules; betarules)
open Test.Specs.STLC.combinators

private
  variable
    γ : Scope

open β-rule

------------------------------------------------------
-- β-reduction tests
------------------------------------------------------

module βredtests where

  test1 : Failable (Term compu 0)
  test1 = reduce betarules (lam (~ ze)) (α ⇨ α) a
  
  _ : test1 ≡ succeed (a ∷ α)
  _ = refl
  
  -- function as input
  test2 : Failable (Term compu 0)
  test2 = reduce betarules (lam (~ ze)) ((α ⇨ α) ⇨ (α ⇨ α)) (lam (~ ze))
  
  _ : test2 ≡ succeed (lam (~ ze) ∷ (α ⇨ α))
  _ = refl
  
  -- take in a function, an argument and apply them
  func : Term const γ
  func = lam (lam (thunk (app (var (su ze)) (~ ze))))
  
  ftype : Term const γ
  ftype = (α ⇨ α) ⇨ α ⇨ α
  
  arg1  : Term const γ
  arg1 = lam (~ ze)
  
  reducable-term : Term compu 1
  reducable-term = elim (elim (func ∷ ftype) arg1) (thunk (var ze))
  
  test3 : Failable (Term compu 0)
  test3 = reduce betarules func ftype arg1
  
  _ : test3 ≡ succeed (lam (thunk (app (arg1 ∷ (α ⇨ α)) (~ ze))) ∷ (α ⇨ α))
  _ = refl

------------------------------------------------------
-- normalization tests
------------------------------------------------------

module normtests where

  open import TypeChecker using (infer)
  open import BwdVec

  -- take in a function, an argument and apply them
  func : Term const γ
  func = lam (lam (thunk (app (var (su ze)) (~ ze))))
  
  ftype : Term const γ
  ftype = (α ⇨ α) ⇨ α ⇨ α
  
  arg1  : Term const γ
  arg1 = lam (~ ze)
  
  reducable-term : Term compu 1
  reducable-term = elim (elim (func ∷ ftype) arg1) (thunk (var ze))


  -- should perform a single reduction

  test1 : Term const 0
  test1 = normalize betarules (infer rules) ε (thunk (app (lam (~ ze) ∷ (α ⇨ α)) a))

  _ : test1 ≡ a
  _ = refl

  -- should reduce multiple nested eliminations

  test2 : Term const 1
  test2 = normalize betarules (infer rules) (ε -, α) reducable-term
  
  _ : test2 ≡ thunk (var ze)
  _ = refl

  -- should normalize under a binder

  test3 : Term const 0
  test3 = normalize betarules (infer rules) ε (lam (thunk (app (lam (~ ze) ∷ (α ⇨ α)) a)))

  _ : test3 ≡ lam a
  _ = refl

  -- should normalize the eliminator, even if the target is neutral

  test4 : Term const 1
  test4 = normalize betarules (infer rules) (ε -, α) (app (var ze) (thunk (app (lam (~ ze) ∷ (α ⇨ α)) a)))

  _ : test4 ≡ thunk (app (var ze) a)
  _ = refl

  -- should normalize the target even if it results in a neutral term

  test5 : Term const 1
  test5 = normalize betarules (infer rules) (ε -, α) (app (app (lam (~ (su ze)) ∷ (α ⇨ α)) a) a)

  _ : test5 ≡ thunk (app (var ze) a)
  _ = refl



