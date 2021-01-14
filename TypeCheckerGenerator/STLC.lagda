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
open import Rules using (ElimRule; TypeRule; UnivRule; Rules; rs; ∋rule; ε; _placeless; type; _⇉_; _⊢'_; _∋'_[_]; `)
open import Thinning using (Ø; _O; ε; ι)
open import Data.Product using (_,_)
open ElimRule
open TypeRule
open UnivRule
open ∋rule
\end{code}

\begin{code}
-- Can we model STLC?

-- we have a universe
U : Pattern 0
U = ` 'U'

U-type : TypeRule -- UnivRule U U (ε ((` '⊤') placeless))
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

a-rule : ∋rule -- CheckRule α a α (ε (a placeless))
subject  a-rule = a
input    a-rule = α
premises a-rule = (` 'α') , (ε (a placeless))

{-
β : Pattern 0
β = ` 'β'

β-rule : TypeRule 
subject  β-rule = β
premises β-rule = (` '⊤') , (ε (β placeless))

β-inuniv : ∋rule
subject  β-inuniv = β
input    β-inuniv = U
premises β-inuniv = (` 'U') , (ε (β placeless))
-}

-- REMEMEBER TO ADD TO RULES WHEN UNCOMMENTING

{-
-- and a value 'b'
b : Pattern 0
b = ` 'b'

b-rule : ∋rule
subject  b-rule = b
input    b-rule = β
premises b-rule = (` 'β') , (ε (b placeless))
-}

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
--ε (lam placeless)

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
typerules = U-type ∷ α-rule ∷ ⇛-rule ∷ [] -- add β-rule

univrules : List UnivRule
univrules = U-univ  ∷ [] -- add

∋rules : List ∋rule
∋rules = lam-rule ∷ α-inuniv ∷ a-rule ∷ ⇛-inuniv ∷ [] -- add b-rules

elimrules : List ElimRule
elimrules = app-rule ∷ []

rules : Rules
rules = rs typerules univrules ∋rules elimrules





















































































--ok let's try typing some stuff

open import TypeChecker using (check; infer)
open import CoreLanguage
open import Failable
open import Data.String using (String)

-- this should infer the type α → α

radtest : Term lib compu 0
radtest = ess (bind (thunk (var ze))) ∷ ess (ess (` 'α') ∙ ess (ess (` '→') ∙ ess (` 'α')))

result : String
result with infer rules ε radtest
... | succeed x = print x
... | fail x    = x

-- this should infer type α

apptest : Term lib compu 0
apptest = ess (elim radtest (ess (` 'a')))

resultapp : String
resultapp with infer rules ε apptest
... | succeed x = print x
... | fail x    = x

-- this should inter type (α → α) → (α → α)
α→α : Term lib const 0
α→α = ess ((ess (` 'α') ∙ ess (ess (` '→') ∙ ess (` 'α'))))

[α→α]→[α→α] : Term lib const 0
[α→α]→[α→α] = ess (α→α ∙ ess (ess (` '→') ∙ α→α))

identityreturner : Term lib compu 0
identityreturner = ess (bind (thunk (var ze))) ∷ [α→α]→[α→α]

resultidreturn : String
resultidreturn with infer rules ε identityreturner
... | succeed x = print x
... | fail x    = x

-- and finally if we apply the id returner to the id function we should get the id function
-- a.k.a should infer type 

returnerapplied : Term lib compu 0
returnerapplied = ess (elim identityreturner (ess (bind (thunk (var ze)))))

resultreturnerapplied : String
resultreturnerapplied with infer rules ε returnerapplied
... | succeed x = print x
... | fail x    = x

--we can also have an elimination in the eliminator position of an elimination
-- BUG FOUND!!!
elimeverywhere : Term lib compu 0
elimeverywhere = ess (elim
                       (ess (bind (thunk (elim (ess (var ze)) (ess (` 'a'))))) ∷ ess (α→α ∙ ess (ess (` '→') ∙ ess (` 'α'))))
                       (thunk (elim identityreturner (ess (bind (thunk (var ze))))))
                     )

resultelimeverywhere : String
resultelimeverywhere with infer rules ε  elimeverywhere
... | succeed x = print x
... | fail x    = x

-- \end{code}
