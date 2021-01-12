\section{Thinnings}

\begin{code}
module Thinning where

open import CoreLanguage
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Bool using (Bool)
open import Data.Empty renaming (⊥ to bot)
open import Data.Unit renaming (⊤ to top)
\end{code}

\begin{code}
private
  variable
    γ : Scope
    γ' : Scope
    δ : Scope
    δ' : Scope
    γ₁ : Scope
    γ₂ : Scope
    γ₃ : Scope

-- things can be scoped
Scoped = Scope → Set

-- ⊥ scope
⊥ : Scoped
⊥ = λ _ → bot

-- ⊤ scope
⊤ : Scoped
⊤ = λ _ → top

-- a thinning
data _⊑_ : Scope → Scope → Set where
  ε   : 0 ⊑ 0
  _O  : (θ : γ ⊑ δ) → γ ⊑ suc δ
  _I  : (θ : γ ⊑ δ) → suc γ ⊑ suc δ

-- identity thinning
ι : {γ : Scope} → γ ⊑ γ
ι {zero}  = ε
ι {suc γ} = ι I

-- empty thinning
Ø : {γ : Scope} → 0 ⊑ γ
Ø {zero}  = ε
Ø {suc γ} = Ø O

-- Thinnability
Thinnable : Scoped → Set
Thinnable X = ∀ {δ} {γ} → X δ → (δ ⊑ γ) → X γ

-- Selectability (the opposite of thinning)
Selectable : Scoped → Set
Selectable X = ∀ {δ} {γ} → (δ ⊑ γ) → X γ → X δ

-- Composability
Composable : (Scope → Scope → Set) → Set
Composable X = ∀ {γ} {γ'} {γ''} → (X γ γ') → (X γ' γ'') → (X γ γ'')

-- thinning composition
-- action of a thinning on a thining
_∘_ : Thinnable (γ₁ ⊑_)
ε     ∘  ε    = ε
θ     ∘ (ϕ O) = (θ ∘ ϕ) O
(θ O) ∘ (ϕ I) = (θ ∘ ϕ) O
(θ I) ∘ (ϕ I) = (θ ∘ ϕ) I

-- variables are thinnable
_⟨var_ : Thinnable Var
ze   ⟨var (θ O)  = su (ze ⟨var θ)
ze   ⟨var (θ I)  = ze
su v ⟨var (θ O)  = su (su v ⟨var θ)
su v ⟨var (θ I)  = su (v ⟨var θ)

-- variables are singleton thinnings
⟦_⟧var : Var γ → 1 ⊑ γ
⟦_⟧var {suc s} ze     = Ø I
⟦_⟧var {suc s} (su v) = ⟦ v ⟧var O

private
  variable
    l : Lib
    d : Dir
    X : Set
    Y : Set
    n : ℕ

-- terms are thinnable
_⟨term_ : Thinnable (Term l d)
_⟨term_ {ess} {const} (` x)      θ  = ` x
_⟨term_ {ess} {const} (s ∙ t)    θ  = (s ⟨term θ) ∙ (t ⟨term θ)
_⟨term_ {ess} {const} (bind t)   θ  = bind (t ⟨term (θ I))
_⟨term_ {ess} {compu} (var x)    θ  = var (x ⟨var θ)
_⟨term_ {ess} {compu} (elim e s) θ  = elim (e ⟨term θ) (s ⟨term θ)
_⟨term_ {lib} {const} (ess x)    θ  = ess (x ⟨term θ)
_⟨term_ {lib} {const} (thunk x)  θ  = thunk (x ⟨term θ)
_⟨term_ {lib} {compu} (ess x)    θ  = ess (x ⟨term θ)
_⟨term_ {lib} {compu} (t ∷ T)    θ  = (t ⟨term θ) ∷ (T ⟨term θ)

-- selection
data BwdVec (X : Set) : ℕ → Set where
  ε    : BwdVec X 0
  _-,_ : {n : ℕ} → BwdVec X n → X → BwdVec X (suc n)

infixl 20 _-,_

map : (X → Y) → BwdVec X n → BwdVec Y n
map f ε = ε
map f (xs -, x) = map f xs -, f x

-- trim m things off the front
trim : (m : ℕ) → BwdVec X n → BwdVec X (n ∸ m)
trim zero    v        = v
trim (suc m)  ε       = ε
trim (suc m) (v -, x) = trim m v

_!_ : Selectable (BwdVec X)
ε     ! ε         = ε
(θ O) ! (xs -, x) = θ ! xs
(θ I) ! (xs -, x) = (θ ! xs)-, x


-- injections
_◃_ : (γ : Scope) → (δ : Scope) → γ ⊑ (δ + γ)
γ ◃ zero   = ι
γ ◃ suc δ  = (γ ◃ δ) O

_▹_ : (γ : Scope) → (δ : Scope) → δ ⊑ (δ + γ)
γ ▹ zero   = Ø
γ ▹ suc δ  = (γ ▹ δ) I

-- substitution
_⇒[_]_ : Scope → Scoped → Scope → Set
γ ⇒[ X ] δ = BwdVec (X δ) γ

_⇒_ : Scope → Scope → Set
γ ⇒ δ = γ ⇒[ Term lib compu ] δ

-- we can select from substitions using _!_

-- we can lookup things in substitutions
lookup : (T : Scoped) → δ ⇒[ T ] γ → Var δ → T γ
lookup T (σ -, x) ze = x
lookup T (σ -, x) (su v) = lookup T σ v

-- Substitutability
Substitutable : Scoped → Set
Substitutable T = ∀ {γ} {γ'} → T γ → γ ⇒[ T ] γ' → T γ'

-- substitution composability
[_]_∘σ_ : ∀ {T} → Substitutable T → Composable _⇒[ T ]_
[ / ]  ε       ∘σ σ' = ε
[ / ] (σ -, x) ∘σ σ' = ([ / ] σ ∘σ σ') -, / x σ'

-- and substitutions are thinnable
-- if the thing it is substituting is thinnable
⟨sub : ∀ {T} → Thinnable T → Thinnable (δ ⇒[ T ]_)
⟨sub ⟨T ε θ        = ε
⟨sub ⟨T (σ -, x) θ = ⟨sub ⟨T σ θ -, ⟨T x θ

-- weakening
Weakening : Set
Weakening = ∀ {γ} → γ ⊑ (suc γ)

↑ : Weakening
↑ {γ} = ι O

-- a Weakening has an action on a Weakenable thing
Weakenable : Scoped → Set
Weakenable T = ∀ {γ} → T γ → T (suc γ)

-- we can weaken anything thinnable
weaken : {T : Scoped} → Thinnable T → Weakenable T
weaken {T} ⟨ t = ⟨ t ↑

-- variables are weakenable
_^var : Weakenable Var
_^var = weaken _⟨var_

-- so for a start we can weaken thinnings themselves
_^ : Weakenable (γ ⊑_)
_^ = weaken _∘_

-- substitutions are Weakenable if the thing
-- they substitute is Thinnable

^sub : ∀ {T} → Thinnable T → Weakenable (δ ⇒[ T ]_)
^sub ⟨T ε                  = ε
^sub ⟨T {γ} (_-,_ {n} σ x) = (^sub ⟨T {γ} σ) -, weaken ⟨T x

-- 'Term lib compu' substitutions are thinnable
private
  variable
    δ` : Scope

_⟨σ_ : Thinnable (γ ⇒_)
σ ⟨σ θ = ⟨sub _⟨term_ σ θ

_^` : (γ ⇒ δ) → γ ⇒ (suc δ)
σ ^` = σ ⟨σ ↑

-- action of a substitution
_/term_ : Term l d γ → γ ⇒ δ → Term lib d δ

_/term_ {ess} {const} (` x)       σ  = ess (` x)
_/term_ {ess} {const} (s ∙ t)     σ  = ess ((s /term σ) ∙ (t /term σ))
_/term_ {ess} {const} (bind t)    σ  = ess (bind (t /term (σ ^` -, ess (var ze))))

_/term_ {ess} {compu} (var v)     σ  with ⟦ v ⟧var ! σ
...                                 | ε -, x        = x
_/term_ {ess} {compu} (elim e s)  σ  = ess (elim (e /term σ) (s /term σ))

_/term_ {lib} {const} (ess x)     σ  = x /term σ
_/term_ {lib} {const} (thunk x)   σ  = ↠ (x /term σ)
_/term_ {lib} {compu} (ess x)     σ  = x /term σ
_/term_ {lib} {compu} (t ∷ T)     σ  = (t /term σ) ∷ (T /term σ)

-- terms are weakenable
_^term : Weakenable (Term l d)
_^term {l} {d} t = weaken {Term l d} _⟨term_ t

-- identity substitution
ι⇒ : γ ⇒ γ
ι⇒ {zero}  = ε
ι⇒ {suc γ} = (ι⇒ ^`) -, ess (var ze)

-- substitution composition
_∘ₛ_ : (γ₁ ⇒ γ₂) → (γ₂ ⇒ γ₃) → (γ₁ ⇒ γ₃)
ε        ∘ₛ ρ = ε
(σ -, x) ∘ₛ ρ = (σ ∘ₛ ρ) -, (x /term ρ)

\end{code}
