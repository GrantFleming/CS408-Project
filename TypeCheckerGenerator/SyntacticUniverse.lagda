\section{A Syntactic Universe}

\hide{
\begin{code}
module SyntacticUniverse where
\end{code}

\begin{code}
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Context using (Var; Bwd; _-,_)
\end{code}
}

\hide{
\begin{code}
private
  variable
    X  : Set
    Γ  : Bwd X
\end{code}
}

\begin{code}
data Desc (X : Set) : Set₁ where
  tag   : (T : Set) → (T → Desc X) → Desc X
  bind  : X → Desc X → Desc X
  term  : X → Desc X  
  pair  : Desc X → Desc X → Desc X
  unit  : Desc X
\end{code}

\begin{code}
⟦_⟧ : Desc X → (X → Bwd X → Set) → Bwd X → Set
⟦ tag T cD ⟧    Ρ Γ  = Σ[ t ∈ T ] ⟦ cD t ⟧ Ρ Γ
⟦ bind x D ⟧    Ρ Γ  = ⟦ D ⟧ Ρ (Γ -, x)
⟦ term x ⟧      Ρ Γ  = Ρ x Γ
⟦ pair D¹ D² ⟧  Ρ Γ  = ⟦ D¹ ⟧ Ρ Γ × ⟦ D² ⟧ Ρ Γ
⟦ unit ⟧        Ρ Γ  = ⊤
\end{code}


\begin{code}
data Term (F : X → Desc X)(x : X)(Γ : Bwd X) : Set where
  var  : Var x Γ → Term F x Γ
  con  : ⟦ F x ⟧ (Term F) Γ  → Term F x Γ
\end{code}

\subsection{Describing a Generic Language}
