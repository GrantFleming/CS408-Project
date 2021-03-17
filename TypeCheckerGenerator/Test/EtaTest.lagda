\hide{
\begin{code}
module Test.EtaTest where

open import Test.Specs.STLC using (etarules; lam-ηrule; betarules; rules)
open Test.Specs.STLC.combinators
open import CoreLanguage
open import Pattern
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import EtaRule
open import Data.Maybe using (Maybe; just; nothing)
open η-Rule
open import Thinning using (_^term)
open import Failable
open import Data.List using ([])
\end{code}
}
\begin{code}
---------------------------------------------
-- Test 1:
-- η expanding λx.a = λy.(λx.a y)
---------------------------------------------

test1 : Const 0
test1 = lam a

test1type : Const 0
test1type = α ⇨ α

_ : η-match lam-ηrule test1type ≡ succeed ((thing α) ∙ (` ∙ (thing α)))
_ = refl

_ : η-expand lam-ηrule test1type test1 ≡ lam (thunk (elim ((test1 ^term) ∷ (test1type ^term)) (~ ze)))
_ = refl


--------------------------------------------------
-- Test 2:
-- η expanding ((λx.λy.x) b) = λy.(((λx.λy.x) b) y)
---------------------------------------------------

test2 : Const 0
test2 = thunk (elim (lam (lam (~ (su ze))) ∷ (β ⇨ α ⇨ β)) b)

test2type : Const 0
test2type = α ⇨ β

_ : η-match lam-ηrule test2type ≡ succeed ((thing α) ∙ (` ∙ (thing β)))
_ = refl

_ : η-expand lam-ηrule test2type test2 ≡ lam (thunk (elim (↞↞ (test2 ^term) (test2type ^term)) (~ ze)))
_ = refl

\end{code}
