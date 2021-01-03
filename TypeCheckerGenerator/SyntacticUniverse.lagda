\section{A Syntactic Universe}

\hide{
\begin{code}
module SyntacticUniverse where
\end{code}

\begin{code}
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
\end{code}
}

In order that we might program in a syntax independent way, we introduce
our syntactic universe.

\hide{
\begin{code}
data Bwd (A : Set) : Set where
  ε     : Bwd A
  _-,_  : Bwd A → A → Bwd A

private
  variable
    X : Set
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

\subsection{Describing a Generic Language}

We now have the required elements to describe a generic language.

