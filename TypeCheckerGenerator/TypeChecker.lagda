\section{Checking Types}

\begin{code}
module TypeChecker where


\end{code}

\begin{code}
data Ty : Set where
  sometypes : Ty
  _constructors_ : Ty → Ty → Ty

import SyntacticUniverse
open module SynU = SyntacticUniverse Ty

data TaggingConstruct : Set where
  things : TaggingConstruct
  otherthing : TaggingConstruct
  

lang : Ty → Desc Ty
lang τ = tag TaggingConstruct (λ where
                                things → unit
                                otherthing → unit)

Tm : ContextState → Ty → Set
Tm Γ τ = Term lang τ Γ

\end{code}
