\section{A Syntactic Universe}

\hide{
\begin{code}
module SyntacticUniverse where
\end{code}

\begin{code}
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Unit
open import Data.Empty
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Context using (Bwd; ε; _-,_; Var)
\end{code}
}

\hide{
\begin{code}
private
  variable
    X : Set
    Γ : Bwd X
    m : ℕ
    n : ℕ
\end{code}
}

\begin{code}
data Desc (X : Set) : Set₁ where
  tag   : (A : Set) → (A → Desc X) → Desc X
  bind  : X → Desc X → Desc X
  term  : X → Desc X
  pair  : Desc X → Desc X → Desc X
  unit  : Desc X
\end{code}

\begin{code}
⟦_⟧ : Desc X → (X → Bwd X → Set) → Bwd X → Set
⟦ tag A cD ⟧    Ρ Γ  = Σ[ a ∈ A ] ⟦ cD a ⟧ Ρ Γ
⟦ bind x D ⟧    Ρ Γ  = ⟦ D ⟧ Ρ (Γ -, x)
⟦ term x ⟧      Ρ Γ  = Ρ x Γ
⟦ pair D¹ D² ⟧  Ρ Γ  = ⟦ D¹ ⟧ Ρ Γ × ⟦ D² ⟧ Ρ Γ
⟦ unit ⟧        Ρ Γ  = ⊤

\end{code}

\begin{code}
data Term (describe : X → Desc X)(x : X)(Γ : Bwd X) : Set where
  var  : Var x Γ → Term describe x Γ
  con  : ⟦ describe x ⟧ (Term describe) Γ  → Term describe x Γ
\end{code}

\subsection{Describing a Generic Language}

We now have the required elements to describe a generic language.

