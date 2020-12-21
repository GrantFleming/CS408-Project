\section{A Syntactic Universe}

\hide{
\begin{code}
module SyntacticUniverse where
\end{code}

\begin{code}
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Nat using (ℕ)
open import Pattern using (Pattern)
open import Context using (Bwd; ε; _-,_; Var)
open import Level
\end{code}
}

In order that we might program in a syntax independent way, we introduce
our syntactic universe.

\hide{
\begin{code}
private
  variable
    X : Set₁
    Γ : Bwd X
    m : ℕ
    n : ℕ
\end{code}
}

\begin{code}
data Desc (X : Set₁) : Set₂ where
  tag   : (A : Set₁) → (A → Desc X) → Desc X
  bind  : X → Desc X → Desc X
  term  : X → Desc X
  pair  : Desc X → Desc X → Desc X
  unit  : Desc X
\end{code}

\begin{code}
data ⊤ : Set₁ where
  tt : ⊤

⟦_⟧ : Desc X → (X → Bwd X → Set₁) → Bwd X → Set₁
⟦ tag A cD ⟧    Ρ Γ  = Σ[ a ∈ A ] ⟦ cD a ⟧ Ρ Γ
⟦ bind x D ⟧    Ρ Γ  = ⟦ D ⟧ Ρ (Γ -, x)
⟦ term x ⟧      Ρ Γ  = Ρ x Γ
⟦ pair D¹ D² ⟧  Ρ Γ  = ⟦ D¹ ⟧ Ρ Γ × ⟦ D² ⟧ Ρ Γ
⟦ unit ⟧        Ρ Γ  = ⊤

\end{code}

\begin{code}
data Term (describe : X → Desc X)(x : X)(Γ : Bwd X) : Set₁ where
  var  : Var x Γ → Term describe x Γ
  con  : ⟦ describe x ⟧ (Term describe) Γ  → Term describe x Γ
\end{code}

\subsection{Describing a Generic Language}

We now have the required elements to describe a generic language.


\begin{code}
-- types are just patterns with a single hole
-- type constructors are patterns with multiple holes
Ty = Pattern

data IorE : Set₁ where intro elim : IorE

desc-intro : Ty → Desc Ty
desc-intro = {!!}

desc-elim : Ty → Desc Ty
desc-elim = {!!}

lang : Ty → Desc Ty
lang τ = tag IorE (λ where
                     intro → tag Ty {!!}
                     elim  → tag Ty {!!})

Tm : Bwd Ty → Ty → Set₁
Tm Γ τ = Term lang τ Γ
\end{code}

\begin{code}

open import Data.List using (List; _∷_; [])

lamTy : Pattern
Pattern.name  lamTy = 0
Pattern.holes lamTy = {!!} ∷ []

idFunc : Tm ε lamTy
idFunc = con (intro , {!!})

\end{code}
