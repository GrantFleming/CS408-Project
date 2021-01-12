\section{A core language}

\hide{
\begin{code}
module CoreLanguage where
\end{code}

\begin{code}
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Unit using (⊤)
open import Data.Char using (Char)
open import Data.List
\end{code}
}

\begin{code}
Scope = ℕ

data Var : Scope → Set where
  ze : {s : Scope} → Var (suc s)
  su : {s : Scope} → Var s → Var (suc s)

toNum : ∀{γ} → Var γ → ℕ
toNum ze     = 0
toNum (su v) = suc (toNum v)

data Ess-Const (γ : Scope) : Set
data Lib-Const (γ : Scope) : Set
data Ess-Compu (γ : Scope) : Set
data Lib-Compu (γ : Scope) : Set

data Ess-Const γ where
  `      : Char → Ess-Const γ
  _∙_    : Lib-Const γ → Lib-Const γ → Ess-Const γ
  bind   : Lib-Const (suc γ) → Ess-Const γ

infixr 20 _∙_ 

data Lib-Const γ where
  ess    : Ess-Const γ → Lib-Const γ
  thunk  : Ess-Compu γ → Lib-Const γ

data Ess-Compu γ where
  var    : Var γ → Ess-Compu γ
  elim   : Lib-Compu γ → Lib-Const γ → Ess-Compu γ

data Lib-Compu γ where
  ess    : Ess-Compu γ → Lib-Compu γ
  _∷_    : Lib-Const γ → Lib-Const γ → Lib-Compu γ

↠ : ∀ {γ} → Lib-Compu γ → Lib-Const γ
↠ (ess x) = thunk x
↠ (t ∷ T) = t

data Lib : Set where ess lib : Lib
data Dir : Set where const compu : Dir

Term : Lib → Dir → Scope → Set
Term ess const γ = Ess-Const γ
Term ess compu γ = Ess-Compu γ
Term lib const γ = Lib-Const γ
Term lib compu γ = Lib-Compu γ
\end{code}
