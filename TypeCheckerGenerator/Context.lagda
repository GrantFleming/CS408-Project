\section{A Notion of Context}

\hide{
\begin{code}
module Context where
open import Level
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_)
open import undefined
\end{code}
}

In our initial work, we begin with a simple notion of contexts, defining
them as backwards lists of types. We take care to produce a universe independent
implementation so that we might use it with our notion of Pattern.

\begin{code}
data Bwd {ℓ} (A : Set ℓ) : Set ℓ where
  ε    : Bwd A
  _-,_ : Bwd A → A → Bwd A
\end{code}

\hide{
\begin{code}
private
  variable
    ℓ : Level
    X : Set ℓ
    σ : X
    Γ : Bwd X
\end{code}
}

We use a de-bruijn index representation of variables.

\begin{code}
data Var (τ : X) : Bwd X → Set where
  ze : Var τ (Γ -, τ)
  su : Var τ Γ → Var τ (Γ -, σ)
\end{code}

We need a concept of types, specifically, user defined types that we do
not know until runtime. We describe base types as containing simply names,
and Type constructors as Vectors of types. Types are either base types or
type constructors, and we finally have our type for contexts.

\begin{code}
record BaseType : Set where
  field
    name  : ℕ   

record TypeConstructor : Set₁ where
  inductive
  field
    name      : ℕ
    argCount  : ℕ
    args      : Vec (BaseType ⊎ TypeConstructor)  argCount


Ty = BaseType ⊎ TypeConstructor

Context = Bwd Ty
\end{code}
