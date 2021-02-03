\section{Semantics}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Semantics where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Pattern using (Pattern; _∙_; _⊗_; _-Env; match)
open import Context using (Context) renaming (_,_ to _-,_)
open import Expression using (Expr; toTerm)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Failable hiding (_>>=_)
\end{code}
}

\hide{
\begin{code}
private
  variable
    γ : Scope
    d : Dir
\end{code}
}

Given the way that we represent typing rules, our type for $β$-rules
should not look unfamiliar. We match a rule by matching patterns for the
target, target type and eliminator and construct the reduced term
and its type from an expression and the resulting environment we
computed in the matching process.

Since we are matching a rule by matching patterns, the target, type and
eliminator in question must be in weak head normal form \hl{verify} and
so care should be taken to compute these forms before attempting to match
a β-rule.
\begin{code}
record β-rule : Set where
  field
    target      :  Pattern 0
    targetType  :  Pattern 0
    eliminator  :  Pattern 0
    redTerm     :  Expr (target ∙ targetType ∙ eliminator) const 0
    redType     :  Expr (target ∙ targetType ∙ eliminator) const 0

  β-match  :  (targ  :  Term const γ)  →
              (type  :  Term const γ)  →
              (elim  :  Term const γ)  →
              Maybe (((γ ⊗ target)      ∙ 
                      (γ ⊗ targetType)  ∙
                      (γ ⊗ eliminator)) -Env)
  β-match tar ty el = do
                        t-env  ← match tar target
                        ty-env ← match ty targetType
                        e-env  ← match el eliminator
                        just (t-env ∙ ty-env ∙ e-env)
                       where
                         open Data.Maybe
                      

  β-reduce  :  ((γ ⊗ target)      ∙
                (γ ⊗ targetType)  ∙
                (γ ⊗ eliminator)) -Env  →
               Term compu γ
  β-reduce (tenv ∙ tyEnv ∙ eenv)
    = let t = toTerm (tenv ∙ tyEnv ∙ eenv) redTerm in
      let T = toTerm (tenv ∙ tyEnv ∙ eenv) redType in
        t ∷ T
open β-rule        
\end{code}
We then define a function that will attempt a reduction with regards
to a list of β-rules by trying to match and apply a rule.
\begin{code}
reduce : List β-rule              →
         (tar    : Term const γ)  →
         (tType  : Term const γ)  →
         (elim   : Term const γ)  →
         Failable (Term compu γ)
reduce [] ta ty el = fail "Failed to reduce"
reduce (rule ∷ rules) ta ty el
  with β-match rule ta ty el
... | nothing  = reduce rules ta ty el
... | just env = succeed (β-reduce rule env)
\end{code}

Finally we define normalization in terms of a list of β-rules but also
in terms of some function that may infer types for us. In practice we will
supply our type-inference function (defined later) "pre-loaded" with typing
rules.

Our approach to normalization is naive. We make a post-order traversal of
the syntax tree and where processing eliminations, stuck eliminations are
embedded as "thunk" terms (although the target and eliminator are reduced
where possible as would be expected in post order traversal), whereas
reducable eliminations are reduced and the resulting term is also normalized.

As we pass under binders, we must extend the context, however the type of
the newly bound variable is not known and so the context is extended with
a special symbol to indicate this. Later we will see that the parser is
unable to produce this symbol and so it is safe to use for this purpose.
\hl{make sure this is so}. The type-synthesis process will synthesis the
type of a variable by looking it up in the context. During this process
it also checks that what it retrieves from the context is indeed a type.
Since there cannot exists a type rule for $'⊤'$ \hl{(change)} we cannot
successfully infer or check the type for the newly bound variable insuring
that such variables of unknown type cannot involve themselves in
computation in which they have no right.

\begin{itemize}
  \item Normalization by evaluation would be more efficient
  \item The current normalization process has no guarantees w.r.t
        termination
\end{itemize}

\hide{
\begin{code}
{-# TERMINATING #-}
\end{code}
}
\begin{code}
normalize : List β-rule →
            (∀ {δ} → Context δ → Term compu δ → Failable (Term const δ)) →
            Context γ →
            Term d γ →
            Term const γ
normalize rs infer = norm
  where
    norm : Context γ → Term d γ → Term const γ
    norm {d = const} Γ (bind t)   = bind (norm (Γ -, ` "unknown" ) t)
    norm {d = compu} Γ (elim t e) with norm Γ t | norm Γ e
    ... | t' | e' with infer Γ t
    ... | fail m         = thunk (elim t e')
    ... | succeed ty with reduce rs t' ty e'
    ... | succeed x      = norm Γ x
    ... | fail m with t'
    ... | thunk x        = thunk (elim x e')
    ... | _              = thunk (elim (t' ∷ ty) e')
    --- ...
\end{code}
\hide{
\begin{code}
    norm {d = const} Γ (` x)      = ` x
    norm {d = const} Γ (s ∙ t)    = norm Γ s ∙ norm Γ t
    norm {d = const} Γ (thunk x)  = norm Γ x
    norm {d = compu} Γ (var x)    = thunk (var x)
    norm {d = compu} Γ (t ∷ T)    = norm Γ t    
\end{code}
}
