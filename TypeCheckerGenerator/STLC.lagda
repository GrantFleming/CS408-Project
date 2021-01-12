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
open import Data.Product using (_,_)
\end{code}

\begin{code}

-- Can we model STLC?

-- we have a universe
U : Pattern 0
U = ` 'U'

U-type : ConstRule
U-type = TypeRule U (` '⊤') (ε (U placeless))

U-univ : ConstRule
U-univ = UnivRule U U (ε ((` '⊤') placeless))

-- a base type α in the universe

α : Pattern 0
α = ` 'α'

α-rule : ConstRule
α-rule = TypeRule α (` '⊤') (ε (α placeless))

α-inuniv : ConstRule
α-inuniv = CheckRule U α U
           (ε (α placeless)) 

-- which has a single value'a'
a : Pattern 0
a = ` 'a'

a-rule : ConstRule
a-rule = CheckRule α a α (ε (a placeless))

-- and a function type _⇛_ in the universe
⇛ : Pattern 0
⇛ = place Ø ∙ ` '→' ∙ place Ø

⇛-rule : ConstRule
⇛-rule = TypeRule ⇛ ((` '⊤' ∙ place Ø) ∙ place Ø) (type (⋆ ∙) Ø ⇉
                       type (∙ ∙ ⋆) Ø ⇉
                       ε (⇛ placeless))

⇛-inuniv : ConstRule
⇛-inuniv = CheckRule U ⇛ ((U ∙ place Ø) ∙ place Ø)
           (type (⋆ ∙) Ø  ⇉
           type (∙ ∙ ⋆) Ø ⇉
           ε (⇛ placeless))

-- which has lambda terms as it's values
lam : Pattern 0
lam = bind (place (Ø O))

-- we check the type of abstractions
lam-rule : ConstRule
lam-rule = CheckRule ⇛ lam (⇛ ∙ bind (place (Ø O)))
             ((((⋆ ∙) / ε) ⊢' (((∙ ∙ ⋆) / ε) ∋' bind ⋆ [ Ø O ]))
             ⇉ ε (lam placeless))

-- and we can type lam elimination
open ElimRule
app-rule : ElimRule
target     app-rule = 0        -- why 0? come back to this
targetPat  app-rule = ⇛        -- we should be able to infer the target to be a function type
eliminator app-rule = place Ø  -- can be eliminated by anything (syntactically)
premises   app-rule = targetPat app-rule ∙ place Ø ,
                      (((∙ ∙ ⋆) / ε) ∋' ⋆ [ Ø ]) ⇉
                      ε ((` '⊤') placeless)
output     app-rule = ess ((((⋆ ∙) ∙) / ε)   ∙
                      ess (ess (` '→')       ∙
                      (((∙ ∙ ⋆) ∙) / ε)))

open import Data.List using (List; []; _∷_)

constRules : List ConstRule
constRules = U-type ∷ U-univ ∷ α-rule   ∷ α-inuniv ∷
             a-rule ∷ ⇛-rule ∷ ⇛-inuniv ∷ lam-rule ∷ []

elimRules : List ElimRule
elimRules = app-rule ∷ []
\end{code}
