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
open import Expression using (_/_; `; _∙_; _∷_)
open import Rules using (ElimRule; TypeRule; UnivRule; ∋rule; ε; _placeless; type; _⇉_; _⊢'_; _∋'_[_]; `)
open import Thinning using (Ø; _O; ι)
open import BwdVec using (ε)
open import Data.Product using (_,_)
open import TypeChecker using (RuleSet; rs)
open import Semantics renaming (β-rule to β-Rule)
open import BwdVec
open β-Rule
open ElimRule
open TypeRule
open UnivRule
open ∋rule
\end{code}

We begin by introducing some combinators to construct our language terms
as creating these terms directly in our internal language can be tedious.

\begin{code}
module combinators where
  α : ∀{γ} → Term const γ
  α = ` 'α'
  
  a : ∀{γ} → Term const γ
  a = ` 'a'
  
  β : ∀{γ} → Term const γ
  β = ` 'β'
  
  b : ∀{γ} → Term const γ
  b = ` 'b'
  
  _⇨_ : ∀{γ} → Const γ → Const γ → Term const γ
  x ⇨ y = x ∙ ((` '→') ∙ y)
  infixr 20 _⇨_
  
  lam : ∀ {γ} → Term const (suc γ) → Term const γ
  lam t = ` 'λ' ∙ bind t
  
  ~ : ∀ {γ} → Var γ → Term const γ
  ~ vr = thunk (var vr)
  
  app : ∀ {γ} → Compu γ → Const γ → Term compu γ
  app e s = elim e s
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
lam = ` 'λ' ∙ bind (place ι)

-- we check the type of abstractions
lam-rule : ∋rule
subject  lam-rule = lam
input    lam-rule = ⇛
premises lam-rule = input lam-rule ∙ bind (place ι) , (((⋆ ∙) / ε) ⊢' (((∙ ∙ ⋆) / ε) ∋' ∙ bind ⋆ [ ι ]))
                                                      ⇉ ε ((` 'λ' ∙ bind (` '⊤')) placeless)
         
-- and we can type lam elimination
app-rule : ElimRule
targetPat  app-rule = ⇛
eliminator app-rule = place ι
premises   app-rule = targetPat app-rule ∙ place ι ,
                      (((⋆ ∙) / ε) ∋' ⋆ [ ι ]) ⇉
                      ε ((` '⊤') placeless)
output     app-rule = (((∙ ∙ ⋆) ∙) / ε)

-- β rules

app-βrule : β-Rule
target      app-βrule  =  ` 'λ' ∙ bind (place ι)
targetType  app-βrule  =  targetPat app-rule
eliminator  app-βrule  =  place ι
redTerm     app-βrule  =  ((∙ bind ⋆) ∙) / (ε -, (((∙ (∙ ⋆)) / ε) ∷ ((∙ ((⋆ ∙) ∙)) / ε)))
redType     app-βrule  =  (∙ ((∙ ∙ ⋆) ∙)) / ε

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

betarules : List β-Rule
betarules = app-βrule ∷ []

open import undefined
rules : RuleSet
rules =  rs typerules univrules ∋rules elimrules betarules
\end{code}
