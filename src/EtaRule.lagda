\section{η rules}
\label{section-etarules}
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

Later we will show how we might fully normalise a term using a technique
known as normalisation by evaluation. To do this, we will find
that we require the ability to perform $η$-expansion and so we provide a
rule to help us achieve this.

In our η-rule, we store only the eliminator for each place in the pattern.
To generate the η-expanded form, we map the elimination of the target
over this environment of eliminators to get the full eliminations that
are destined for each place in the pattern. This is very straightforward
as a concept but we have to fix up our types a little to convince
Agda of the well-scopedness. We use a mapping function we defined to easily
map over an environment and help us concisely build the eliminations from
the environment of eliminators.
\begin{code}
record η-Rule : Set where
  open ∋rule

  field
    checkRule    :  ∋rule
    eliminators  :  subject checkRule -Env
  headForm = subject checkRule

  eliminations : (type target : Const γ) → (γ ⊗ headForm) -Env
  eliminations {γ} type target
    = map
        (λ {δ} const → thunk (elim ((↞↞ target type) ⟨term (γ ◃ δ)) (γ ⊗term const)))
        eliminators

  η-expand : (type target : Const γ) → Const γ
  η-expand ty tm = termFrom headForm (eliminations ty tm)         
\end{code}
\hide{
\begin{code}
  η-match : (type : Const γ) → Failable ((γ ⊗ input checkRule) -Env)
  η-match ty with  match ty (input checkRule)
  ... | nothing = fail "No match."
  ... | just i = succeed i
open η-Rule  
findRule : List η-Rule → (ty : Const γ) →
           Failable (Σ[ r ∈ η-Rule ] (γ ⊗ ∋rule.input (checkRule r)) -Env)
findRule [] ty  = fail ("no η-rule match for: " ++ print ty)
findRule (r ∷ rs) ty with η-match r ty
... | fail x = findRule rs ty
... | succeed i = succeed (r , i)
\end{code}
}
