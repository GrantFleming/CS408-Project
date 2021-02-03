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
open import Data.String using (_++_)
open import Expression using (toTerm; Con)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Failable using (Failable; succeed; fail)
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
    target targetType eliminator : Pattern 0
    redTerm redType : Con (target ∙ targetType ∙ eliminator) 0

  open Data.Maybe using (_>>=_)

  Rule-Env : {γ : Scope} → Set
  Rule-Env {γ} = ((γ ⊗ target)      ∙ 
                  (γ ⊗ targetType)  ∙
                  (γ ⊗ eliminator)) -Env

  β-match : (targ type elim : Const γ) → Maybe Rule-Env
  β-match tar ty el = do
                        t-env  ← match tar target
                        ty-env ← match ty targetType
                        e-env  ← match el eliminator
                        just (t-env ∙ ty-env ∙ e-env)
                      

  β-reduce  :  Rule-Env {γ} → Compu γ
  β-reduce env
    = toTerm env redTerm ∷ toTerm env redType
open β-rule        
\end{code}
We then define a function that will attempt a reduction with regards
to a list of β-rules by trying to match and apply a rule.
\hide{
\begin{code}
open import Failable using (_>>=_)
\end{code}
}
\begin{code}
findRule : List β-rule →
           (tar type elim : Const γ)  →
           Failable ( Σ[ r ∈ β-rule ] Rule-Env r {γ} )
findRule [] t ty e = fail ("No matching β-rule found for " ++
                           print t ++ " : " ++ print ty ++
                           "eliminated by " ++ print e)
findRule (r ∷ rs) t ty e with β-match r t ty e
... | nothing   = findRule rs t ty e
... | just env  = succeed (r , env)

reduce : List β-rule              →
         (tar type elim : Const γ)  →
         Failable (Compu γ)
reduce rules ta ty el
  = do
      (rule , env) ← findRule rules ta ty el
      succeed (β-reduce rule env)
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
            (∀ {δ} → Context δ → Compu δ → Failable (Const δ)) →
            Context γ →
            Term d γ  →
            Const γ
normalize rs infer = norm
  where
    norm : Context γ → Term d γ → Const γ
    norm {d = const} Γ (bind t)   = bind (norm (Γ -, ` "unknown" ) t)
    norm {d = compu} Γ (elim t e) with norm Γ t | norm Γ e
    ... | thunk x  | e' = thunk (elim x e')
    ... | t'       | e' with infer Γ t
    ...     | fail x     = thunk (elim t e')  -- should never happen
    ...     | succeed ty with reduce rs t' ty e'
    ...         | fail x    = thunk (elim (t' ∷ ty) e')    
    ...         | succeed x = norm Γ x
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
