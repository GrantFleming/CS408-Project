\section{Judgements}

\begin{code}
module Judgement where
\end{code}

\begin{code}
open import CoreLanguage
import Pattern as Pat
open Pat using (Pattern; svar)
open Pat.Expression using (Expression)
open import Thinning using (Scoped; _⊑_; ⊥; ⊤)
open import Context using (Context)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (_because_)
open import Data.Bool using (Bool; true; false)
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
    n : ℕ
    m : ℕ
    X : Set
    Y : Set
    M : Set → Set

data J-Type : Set where
  TY NI UNI : J-Type

_≡ᵇ_ : J-Type → J-Type → Bool
TY  ≡ᵇ TY  = true
NI  ≡ᵇ NI  = true
UNI ≡ᵇ UNI = true
_   ≡ᵇ _   = false

-- TO DO - judgements only have 0 or 1 inputs, no need for vec
input-no : J-Type → ℕ
input-no TY  = 0
input-no NI  = 1
input-no UNI = 1

data Judgements (I : Scoped) (S : Scoped) (O : Scoped) (γ : Scope) : (length : ℕ) → (Vec (Maybe (S γ)) length) → Set
record Judgement (I : Scoped) (S : Scoped) (O : Scoped) (γ : Scope) (s : Maybe (S γ)) : Set

record Judgement I S O γ s where
  inductive
  field
    j-type    : J-Type
    input     : Vec (I γ) (input-no j-type)
    precond   : Judgements I I ⊥ γ ((input-no j-type)) (Data.Vec.map just input)

data Judgements I S O γ where
  ε    : Judgements I S O γ 0 []
  _,_ : {s : Maybe (S γ)} {n : ℕ}{l : Vec (Maybe (S γ)) n} →
        Judgement I S O γ s →
        Judgements I S O γ n l →
        Judgements I S O γ (suc n) (s ∷ l)

open Judgement

-- Now lets build the different types of judgement

-- Type

TYPE : (s : S γ) → Judgement I S O γ (just s)
j-type    (TYPE s) = TY
input     (TYPE s) = []
precond   (TYPE s) = ε

-- Universe
UNIV : I γ → Judgement I S O γ nothing
j-type    (UNIV s) = UNI
input     (UNIV i) = i ∷ []
precond   (UNIV i) = TYPE i , ε

-- Type checking
_∋_ : I γ → (s : S γ) → Judgement I S O γ (just s)
j-type    (T ∋ t) = NI
input     (T ∋ t) = T ∷ []
precond   (T ∋ t) = TYPE T , ε

{-
I don't think these will end up being implemented as judgements.

-- Type Lookup
_:!:_ : (s : S γ) → O γ → Judgement I S O γ (just s)
ino       (x :!: T) = 0
input     (x :!: T) = []
precond   (x :!: T) = ε
ono       (x :!: T) = 1
output    (x :!: T) = T ∷ []
postcond  (x :!: T) = TYPE T , ε


-- Type Equality
_≡_ : I γ → I γ → Judgement I S O γ nothing
ino       (T ≡ T') = 2
input     (T ≡ T') = T ∷ T' ∷ []
precond   (T ≡ T') = TYPE T , TYPE T' , ε
ono       (T ≡ T') = 0
output    (T ≡ T') = []
postcond  (T ≡ T') = ε

-- this feels like some structure that already exists
maybemap : {X : Set} {Y : Set} → (X → Y) → Maybe (List X) → List Y
maybemap f nothing  = []
maybemap f (just x) = Data.List.map f x



-- Context Extension
_⊢_ : I γ →
      (j : {s : S (suc γ)} → Judgement I S O (suc γ) (just s)) →
      Judgement I (λ γ' → {s' : S (suc γ')} → Judgement I S O (suc γ') (just s')) O γ (just j)
ino       (S ⊢ j) = 1
input     (S ⊢ j) = S ∷ []
precond   (S ⊢ j) = TYPE S , ε
ono       (S ⊢ j) = 0
output    (S ⊢ j) = []
postcond  (S ⊢ j) = ε
-}
{-
  IMPORTANT - for _⊢_ to work, when we are processing the Judgements, we must
  check if the subject is another judgement, and recursivly check the preconditions
  and postconditions of the subject.

  I.e. we don't (can't) bake in the preconditions and postconditions
-}

\end{code}
