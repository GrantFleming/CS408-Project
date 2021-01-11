\section{A STLC Example}

\hide{
\begin{code}
module STLC where
\end{code}
}

\begin{code}
import Pattern as Pat
open Pat using (Pattern; `; place; bind; _∙_;  ⋆; _∙; ∙_; svar)
open Pat.Expression using (_/_; ess; `; _∙_)
open import Rules using (ConstRule; ElimRule; TypeRule; UnivRule; CheckRule; ε; _placeless; type; _⇉_; _⊢'_; _∋'_[_])
open import Thinning using (Ø; _O; ε)
\end{code}

\begin{code}

-- Can we model STLC?

-- we have a universe
U : Pattern 0
U = ` 'U'

U-type : ConstRule (` '⊤')
U-type = TypeRule U (ε (U placeless))

U-univ : ConstRule U
U-univ = UnivRule U (ε ((` '⊤') placeless))

-- a base type α in the universe

α : Pattern 0
α = ` 'α'

α-rule : ConstRule (` '⊤')
α-rule = TypeRule α (ε (α placeless))

α-inuniv : ConstRule U
α-inuniv = CheckRule U α
           (ε (α placeless)) 

-- which has a single value'a'
a : Pattern 0
a = ` 'a'

a-rule : ConstRule α
a-rule = CheckRule α a (ε (a placeless))

-- and a function type _⇛_ in the universe
⇛ : Pattern 0
⇛ = place Ø ∙ ` '→' ∙ place Ø

⇛-rule : ConstRule (` '⊤')
⇛-rule = TypeRule ⇛ (type (⋆ ∙) Ø ⇉
                     type (∙ ∙ ⋆) Ø ⇉
                     ε (⇛ placeless))

⇛-inuniv : ConstRule U
⇛-inuniv = CheckRule U ⇛
           (type (⋆ ∙) Ø  ⇉
           type (∙ ∙ ⋆) Ø ⇉
           ε (⇛ placeless))

-- which has lambda terms as it's values
lam : Pattern 0
lam = bind (place (Ø O))

-- we check the type of abstractions
lam-rule : ConstRule ⇛
lam-rule = CheckRule ⇛ lam
             ((((⋆ ∙) / ε) ⊢' (((∙ ∙ ⋆) / ε) ∋' bind ⋆ [ Ø O ]))
             ⇉ ε (lam placeless))

-- and we can type lam elimination
open ElimRule
app-rule : ElimRule
target     app-rule = 0        -- why 0? come back to this
targetPat  app-rule = ⇛        -- we should be able to infer the target to be a function type
eliminator app-rule = place Ø  -- can be eliminated by anything (syntactically)
premises   app-rule = (((∙ ∙ ⋆) / ε) ∋' ⋆ [ Ø ]) ⇉
                      ε ((` '⊤') placeless)
output     app-rule = ess ((((⋆ ∙) ∙) / ε)   ∙
                      ess (ess (` '→')       ∙
                      (((∙ ∙ ⋆) ∙) / ε)))

open import Data.List using (List; []; _∷_)

constRules : List (∀ {p'} {p} → ConstRule {p'} p)
constRules = {!α-rule!} ∷ {!!}
\end{code}
