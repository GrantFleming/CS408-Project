\section{A Syntactic Universe}

\hide{
\begin{code}
module SyntacticUniverse (T : Set) where
\end{code}

\begin{code}
open import Data.Product using (_×_; Σ-syntax)
open import Data.Unit
open import Data.Empty
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Context
open module Context' = Context T
\end{code}
}

\hide{
\begin{code}
private
  variable
    n : ℕ
\end{code}
}

\begin{code}
data Desc (T : Set) : Set₁ where
  tag   : (A : Set) → (A → Desc T) → Desc T
  bind  : T → Desc T → Desc T
  term  : T → Desc T
  pair  : Desc T → Desc T → Desc T
  unit  : Desc T
\end{code}

\begin{code}
⟦_⟧ : Desc T → (∀{m} → T → Context m → Set) → Context n → Set
⟦ tag T cD ⟧    Ρ Γ  = Σ[ t ∈ T ] ⟦ cD t ⟧ Ρ Γ
⟦ bind x D ⟧    Ρ Γ  = ⟦ D ⟧ Ρ (extend Γ x)
⟦ term x ⟧      Ρ Γ  = Ρ x Γ
⟦ pair D¹ D² ⟧  Ρ Γ  = ⟦ D¹ ⟧ Ρ Γ × ⟦ D² ⟧ Ρ Γ
⟦ unit ⟧        Ρ Γ  = ⊤
\end{code}


\begin{code}
data Term (F : T → Desc T)(t : T)(Γ : Context n) : Set where
  var  : FVar t Γ → Term F t Γ
  con  : ⟦ F t ⟧ (Term F) Γ  → Term F t Γ
\end{code}

\subsection{Describing a Generic Language}
