\section{η-Rules}
\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module EtaRule where
\end{code}
}
\hide{
\begin{code}
open import CoreLanguage
open import Rules using (∋rule)
open import Pattern using (Pattern; _-Env; termFrom; _⊗_;
                           _⊗term_; match; map)
open import Thinning using (_⟨term_; _◃_)                           
open import Data.List using (List)
open import Data.Product using (Σ-syntax; _,_)
open import Function using (_∘_)
open import Data.Maybe using (just; nothing)
open import Failable
open import Data.List using ([]; _∷_)
open import Data.String using (_++_)
\end{code}
}
\hide{
\begin{code}
private
  variable
    δ : Scope
    γ : Scope
    d : Dir
    p : Pattern γ
\end{code}
}

Later we will show how we might fully normalize a term using a technique
known as normalization by evaluation. In order to do this, we will find
that we require the ability to perform $η$-expansion.

In a future draft of this work, we may include a way that we can
synthesize such rules from other information that is given. However,
for now, we merely give the type of such rules, and a method of performing
the expansion according to such a rule.

In our η-rule, we store only the eliminator for each place in the pattern,
then to generate the eta expanded form, we map the elimination of the target
over this environment of eliminators to get the full eliminations that
are destined for each place in the pattern. This is very straightforward
as a concept but we have to fix-up out types a little in order to convince
Agda of the well-scopedness.

\begin{code}
record η-Rule : Set where
  open ∋rule

  field
    checkRule    :  ∋rule
    eliminators  :  subject checkRule -Env

  η-match : (type : Const γ) → Failable ((γ ⊗ input checkRule) -Env)
  η-match ty with  match ty (input checkRule)
  ... | nothing = fail "No match."
  ... | just i = succeed i

  eliminations : (type target : Const γ) → (γ ⊗ subject checkRule) -Env
  eliminations {γ} type target
    = map
        (λ {δ} const → thunk (elim ((↞↞ target type) ⟨term (γ ◃ δ)) (γ ⊗term const)))
        eliminators

  η-expand : (type target : Const γ) → Const γ
  η-expand ty tm = termFrom (subject checkRule) (eliminations ty tm)         
\end{code}
\hide{
\begin{code}
open η-Rule  
findRule : List η-Rule → (ty : Const γ) →
           Failable (Σ[ r ∈ η-Rule ] (γ ⊗ ∋rule.input (checkRule r)) -Env)
findRule [] ty  = fail ("no η-rule match for: " ++ print ty)
findRule (r ∷ rs) ty with η-match r ty
... | fail x = findRule rs ty
... | succeed i = succeed (r , i)
\end{code}
}
