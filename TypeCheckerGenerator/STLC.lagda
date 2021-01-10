\section{A STLC Example}

\hide{
\begin{code}
module STLC where
\end{code}
}

\begin{code}
import Pattern as Pat
open Pat using (Pattern; `; place; bind; _∙_;  ⋆; _∙; ∙_)
open Pat.Expression using (_/_)
open import Rules using (Rule; TypeRule; UnivRule; CheckRule; ε; _placeless; type; _⇉_; _⊢'_; _∋'_[_])
open import Thinning using (Ø; _O; ε)
\end{code}

\begin{code}

-- Can we model STLC?

-- we have a universe
U : Pattern 0
U = ` 'U'

U-type : Rule 0 (` '⊤')
U-type = TypeRule U (ε (U placeless))

U-univ : Rule 0 U
U-univ = UnivRule U (ε ((` '⊤') placeless))

-- a base type α in the universe

α : Pattern 0
α = ` 'α'

α-rule : Rule 0 (` '⊤')
α-rule = TypeRule α (ε (α placeless))

α-inuniv : Rule 0 U
α-inuniv = CheckRule U α
           (ε (α placeless)) 

-- which has a single value'a'
a : Pattern 0
a = ` 'a'

a-rule : Rule 0 α
a-rule = CheckRule α a (ε (a placeless))

-- and a function type _⇛_ in the universe
⇛ : Pattern 0
⇛ = place Ø ∙ ` '→' ∙ place Ø

⇛-rule : Rule 0 (` '⊤')
⇛-rule = TypeRule ⇛ (type (⋆ ∙) Ø ⇉
                     type (∙ ∙ ⋆) Ø ⇉
                     ε (⇛ placeless))

⇛-inuniv : Rule 0 U
⇛-inuniv = CheckRule U ⇛
           (type (⋆ ∙) Ø  ⇉
           type (∙ ∙ ⋆) Ø ⇉
           ε (⇛ placeless))

-- which has lambda terms as it's values
lam : Pattern 0
lam = bind (place (Ø O))

-- we check the type of abstractions
lam-rule : Rule 0 ⇛
lam-rule = CheckRule ⇛ lam
             ((((⋆ ∙) / ε) ⊢' (((∙ ∙ ⋆) / ε) ∋' bind ⋆ [ Ø O ]))
             ⇉ ε (lam placeless))

-- and we can type lam elimination

-- TO DO
\end{code}
