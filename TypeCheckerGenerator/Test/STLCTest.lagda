\hide{
\begin{code}
module Test.STLCTest where
\end{code}
}

\hide{
\begin{code}
import Test.Specs.STLC as STLC
open import CoreLanguage
open import Failable
open STLC using (rules)
open STLC.combinators
open import Thinning using (ε; _-,_)
open import TypeChecker using (infer)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}
}

\begin{code}

-- should check annotated terms are typed:

_ : infer rules ε (lam (~ ze) ∷ (α ⇨ α)) 
    ≡
    succeed (α ⇨ α)
_ = refl

_ : infer rules ε (α ∷ (α ⇨ α))
    ≡
    fail "failed ∋-check: α→α ∋ α"
_ = refl

-- should check applications are typed:

_ : infer rules ε (app (lam (~ ze) ∷ (α ⇨ α)) a) 
    ≡
    succeed α
_ = refl

_ : infer rules ε (app (lam (~ ze) ∷ ((α ⇨ α) ⇨ (α ⇨ α))) (lam (~ ze))) 
    ≡
    succeed (α ⇨ α)
_ = refl

_ : infer rules ε (app ((lam b) ∷ (α ⇨ β)) a) 
    ≡
    succeed β
_ = refl

_ : infer rules ε (app
         ((lam (thunk (elim (ess (var ze)) (ess (` 'a'))))) ∷ ((α ⇨ α) ⇨ α))
         (thunk (elim (ess (bind (thunk (var ze))) ∷ ((α ⇨ α) ⇨ (α ⇨ α))) (ess (bind (thunk (var ze))))))) 
    ≡
    succeed α
_ = refl

_ : infer rules (ε -, (α ⇨ α) -, β) (ess (bind (thunk (elim (ess (var (su (su ze)))) (ess (` 'a'))))) ∷ (β ⇨ α))
    ≡
    succeed (β ⇨ α)
_ = refl

-- should check the target of elimination first:

_ : infer rules ε (app ((lam a) ∷ (α ⇨ β)) b)
    ≡
    fail "failed ∋-check: β ∋ a"
_ = refl

-- if target of elimination passes typchecking, should check the eliminator:

_ : infer rules ε (app (lam (thunk (var ze)) ∷ (α ⇨ α)) b)
    ≡
    fail "failed ∋-check: α ∋ b"
_ = refl

-- should correctly type nested eliminations

_ : infer rules ε
     (ess
       (elim
         (ess (bind (thunk
            (elim
              (ess (var ze))
              (ess (` 'a'))))) ∷ ess ((α ⇨ α) ∙ ess (ess (` '→') ∙ ess (` 'α'))))
         (thunk
           (elim
             (ess (bind (thunk (var ze))) ∷ ((α ⇨ α) ⇨ (α ⇨ α)))
             (ess (bind (thunk (var ze))))))))
    ≡
    succeed α
_ = refl
\end{code}
