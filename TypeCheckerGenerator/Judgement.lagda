\section{Judgements}

\begin{code}
module Judgement where
\end{code}

\begin{code}
open import CoreLanguage
open import Pattern using (Pattern; Expression; svar)
open import Thinning using (Scoped; _⊑_; ⊥; ⊤)
open import Context using (Context)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Nat using (suc)
\end{code}

\begin{code}
private
  variable
    δ : Scope
    l : Lib
    d : Dir
    p : Pattern 0
    γ : Scope
    I : Scoped
    S : Scoped
    O : Scoped

record Judgement (I : Scoped) (S : Scoped) (O : Scoped) (γ : Scope) : Set where
  inductive
  field
    precond   : Maybe (List (Judgement I I ⊥ γ))
    input     : Maybe (List (I γ))
    subject   : Maybe (S γ)
    output    : Maybe (List (O γ))
    postcont  : Maybe (List (Judgement I O ⊥ γ))

open Judgement

-- Now lets build the different types of judgement

-- Type

TYPE : S γ → Judgement I S O γ
precond   (TYPE s) = nothing
input     (TYPE s) = nothing
subject   (TYPE s) = just s
output    (TYPE s) = nothing
postcont  (TYPE s) = nothing

-- Universe
UNIV : I γ → Judgement I S O γ
precond   (UNIV i) = just (TYPE i ∷ [])
input     (UNIV i) = just (i ∷ [])
subject   (UNIV i) = nothing
output    (UNIV i) = nothing
postcont  (UNIV i) = nothing

-- Type checking
_∋_ : I γ → S γ → Judgement I S O γ
precond   (T ∋ t) = just (TYPE T ∷ [])
input     (T ∋ t) = just (T ∷ [])
subject   (T ∋ t) = just t
output    (T ∋ t) = nothing
postcont  (T ∋ t) = nothing

-- Type Synthesis
_∈_ : S γ → O γ → Judgement I S O γ
precond   (t ∈ T) = nothing
input     (t ∈ T) = nothing
subject   (t ∈ T) = just t
output    (t ∈ T) = just (T ∷ [])
postcont  (t ∈ T) = just (TYPE T ∷ [])

-- Type Lookup
_:!:_ : S γ → O γ → Judgement I S O γ
precond   (x :!: T) = nothing
input     (x :!: T) = nothing
subject   (x :!: T) = just x
output    (x :!: T) = just (T ∷ [])
postcont  (x :!: T) = just (TYPE T ∷ [])

-- Type Equality
_≡_ : I γ → I γ → Judgement I S O γ
precond  (T ≡ T') = just (TYPE T ∷ TYPE T' ∷ [])
input    (T ≡ T') = just (T ∷ T' ∷ [])
subject  (T ≡ T') = nothing
output   (T ≡ T') = nothing
postcont (T ≡ T') = nothing

-- this feels like some structure that already exists
maybemap : {X : Set} {Y : Set} → (X → Y) → Maybe (List X) → List Y
maybemap f nothing  = []
maybemap f (just x) = map f x

-- Context Extension - DANGER! Not Guaranteed to Terminate
{-# NON_TERMINATING #-}
_⊢_ : I γ → Judgement I S O (suc γ) → Judgement I S O γ
precond   (x ⊢ j) = just (TYPE x ∷ maybemap (x ⊢_) (precond j))
input     (x ⊢ j) = just (x ∷ [])
subject   (x ⊢ j) = nothing
output    (x ⊢ j) = nothing
postcont  (x ⊢ j) = just (maybemap (x ⊢_) (postcont j))

\end{code}
