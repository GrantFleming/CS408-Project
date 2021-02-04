\section{η-Rules}
\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module EtaRule where
\end{code}
}
\hide{
\begin{code}
--open import Pattern using (Pattern)
open import CoreLanguage
open import Rules using (∋rule; match-∋rule)
open import Pattern using (Pattern; _-Env; termFrom; _⊗_; `; _∙_; _⊗penv_; _⊗term_;
                           bind; place; match; thing; map)
open import Thinning using (_⟨term_; _^term; _⊑_; _◃_)                           
open import Data.List using (List)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (_∘_)
import Data.Maybe
open import Data.List using ([]; _∷_)
open import Data.String using (_++_)

-- remove me:
open import Data.Nat using (_+_)
\end{code}
}
\hide{
\begin{code}
private
  variable
    δ : Scope
    γ : Scope
\end{code}
}

Later we will show how we might fully normalize a term using a technique
known as normalization by evaluation. In order to do this, we will find
that we require the ability to perform $η$-expansion on our language
constructions.

In a future draft of this work, we may include a way that we can
synthesize such rules from other information that is given. However,
for now, we merely give the type of such rules, and a method of performing
the expansion according to such a rule.

In our η-rule, we store only the eliminator for each place in the pattern,
then to generate the eta expanded form, we map the elimination of the target
over this environment of eliminators to get the full eliminations that
go in each place in the pattern. This is very straightforward as a concept
but we have to fix-up out types a little in order to satisfy the
well-scopedness.

\begin{code}
record η-Rule : Set where
  open ∋rule
  open Data.Maybe using (Maybe; just; _>>=_)

  field
    checkRule   : ∋rule
    eliminators : subject checkRule -Env

  -- perhaps in we don't actually need the environment returned the
  -- way we use this, but it is left for now just incase
  η-match : (type : Const γ) → Maybe ((γ ⊗ input checkRule) -Env)
  η-match ty = match ty (input checkRule)

  eliminations : (type target : Const γ) → (γ ⊗ subject checkRule) -Env
  eliminations {γ} type target
    = map
        (λ {δ} const → thunk (elim ((target ∷ type) ⟨term (γ ◃ δ)) (γ ⊗term const)))
        eliminators

  η-expand : (type term : Const γ) → Const γ
  η-expand = (termFrom (subject checkRule) ∘_) ∘ eliminations
open η-Rule  
\end{code}

We can now provide a function to expand a term given a list of η rules, so
long as we are able to provide the terms type.

\hide{
\begin{code}
open import Failable
open import Data.Maybe using (just; nothing)
\end{code}
}
\begin{code}
expand : List η-Rule → (tm ty : Const γ) → Failable (Const γ)
\end{code}
\hide{
\begin{code}
findRule : List η-Rule → (ty : Const γ) → Failable η-Rule
findRule [] ty = fail ("no η-rule match for: " ++ print ty)
findRule (r ∷ rs) ty with η-match r ty
... | nothing = findRule rs ty
... | just x = succeed r


expand rs tm ty = do
                    r ← findRule rs ty
                    succeed (η-expand r ty tm)
\end{code}
}
