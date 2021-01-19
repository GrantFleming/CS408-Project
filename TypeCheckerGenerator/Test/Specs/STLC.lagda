\section{A STLC Example}

\hide{
\begin{code}
module Test.Specs.STLC where
\end{code}
}

\begin{code}
open import CoreLanguage
open import Data.Nat using (suc)
open import Pattern using (Pattern; `; place; bind; _∙_;  ⋆; _∙; ∙_; svar)
open import Expression using (_/_; ess; `; _∙_)
open import Rules using (ElimRule; TypeRule; UnivRule; Rules; rs; ∋rule; ε; _placeless; type; _⇉_; _⊢'_; _∋'_[_]; `)
open import Thinning using (Ø; _O; ι)
open import BwdVec using (ε)
open import Data.Product using (_,_)
open ElimRule
open TypeRule
open UnivRule
open ∋rule
\end{code}

We begin by introducing some combinators to construct our language terms
as creating these terms directly in our internal language can be tedious.

\begin{code}
module combinators where
  α : ∀{γ} → Term lib const γ
  α = ess (` 'α')
  
  a : ∀{γ} → Term lib const γ
  a = ess (` 'a')
  
  β : ∀{γ} → Term lib const γ
  β = ess (` 'β')
  
  b : ∀{γ} → Term lib const γ
  b = ess (` 'b')
  
  _⇨_ : ∀{γ} → Lib-Const γ → Lib-Const γ → Term lib const γ
  x ⇨ y = ess (x ∙ ess (ess (` '→') ∙ y))
  infixr 20 _⇨_
  
  lam : ∀ {γ} → Term lib const (suc γ) → Term lib const γ
  lam t = ess (bind t)
  
  ~ : ∀ {γ} → Var γ → Term lib const γ
  ~ vr = thunk (var vr)
  
  app : ∀ {γ} → Lib-Compu γ → Lib-Const γ → Term lib compu γ
  app e s = ess (elim e s)

\end{code}

\begin{code}
-- Can we model STLC?

-- we have a universe
U : Pattern 0
U = ` 'U'

U-type : TypeRule
subject  U-type = U
premises U-type = ` '⊤' , (ε (U placeless))

U-univ : UnivRule
input    U-univ = U
premises U-univ = input U-univ , (ε (` '⊤'))

-- a base type α in the universe

α : Pattern 0
α = ` 'α'

α-rule : TypeRule 
subject  α-rule = α
premises α-rule = (` '⊤') , (ε (α placeless))

α-inuniv : ∋rule
subject  α-inuniv = α
input    α-inuniv = U
premises α-inuniv = (` 'U') , (ε (α placeless))

-- which has a value 'a'
a : Pattern 0
a = ` 'a'

a-rule : ∋rule
subject  a-rule = a
input    a-rule = α
premises a-rule = (` 'α') , (ε (a placeless))


β : Pattern 0
β = ` 'β'

β-rule : TypeRule 
subject  β-rule = β
premises β-rule = (` '⊤') , (ε (β placeless))

β-inuniv : ∋rule
subject  β-inuniv = β
input    β-inuniv = U
premises β-inuniv = (` 'U') , (ε (β placeless))


-- REMEMEBER TO ADD TO RULES WHEN UNCOMMENTING


-- and a value 'b'
b : Pattern 0
b = ` 'b'

b-rule : ∋rule
subject  b-rule = b
input    b-rule = β
premises b-rule = (` 'β') , (ε (b placeless))


-- REMEMBER TO ADD RULE TO BOTTOM!!!


-- and a function type _⇛_ in the universe
⇛ : Pattern 0
⇛ = place ι ∙ ` '→' ∙ place ι

⇛-rule : TypeRule
subject  ⇛-rule = ⇛
premises ⇛-rule = ((` '⊤' ∙ place ι) ∙ place ι) , ((type (⋆ ∙) ι ⇉
                                                    type (∙ ∙ ⋆) ι ⇉
                                                    ε (⇛ placeless)))

⇛-inuniv : ∋rule
subject  ⇛-inuniv = ⇛
input    ⇛-inuniv = U
premises ⇛-inuniv = (((U ∙ place ι) ∙ place ι)) , ((type (⋆ ∙) ι  ⇉
                                                    type (∙ ∙ ⋆) ι ⇉
                                                    ε (⇛ placeless)))

-- which has lambda terms as it's values
lam : Pattern 0
lam = bind (place ι)

-- we check the type of abstractions
lam-rule : ∋rule
subject  lam-rule = lam
input    lam-rule = ⇛
premises lam-rule = input lam-rule ∙ bind (place ι) , (((⋆ ∙) / ε) ⊢' (((∙ ∙ ⋆) / ε) ∋' bind ⋆ [ ι ]))
                                                      ⇉ ε (bind (` '⊤') placeless)
         
-- and we can type lam elimination
app-rule : ElimRule
targetPat  app-rule = ⇛
eliminator app-rule = place ι
premises   app-rule = targetPat app-rule ∙ place ι ,
                      (((⋆ ∙) / ε) ∋' ⋆ [ ι ]) ⇉
                      ε ((` '⊤') placeless)
output     app-rule = (((∙ ∙ ⋆) ∙) / ε)

-- first lets get all our rules together:

open import Data.List using (List; []; _∷_)

typerules : List TypeRule
typerules = U-type ∷ α-rule ∷ ⇛-rule ∷ β-rule ∷ [] -- add β-rule

univrules : List UnivRule
univrules = U-univ  ∷ [] -- add

∋rules : List ∋rule
∋rules = lam-rule ∷ α-inuniv ∷ a-rule ∷ ⇛-inuniv ∷ b-rule ∷ [] -- add b-rules

elimrules : List ElimRule
elimrules = app-rule ∷ []

rules : Rules
rules = rs typerules univrules ∋rules elimrules
\end{code}
