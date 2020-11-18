module Unification where

open import Data.Product
open import Data.Bool
open import Data.Unit
open import Data.Nat
open import Function using (case_of_; _∘_)
open import Types
open import Context
open import Lists
open import Fold
import Monads
open Monads.StateMaybe
open Monads.Maybe using (Maybe; just; nothing)

open FTV

foldableFwd : Foldable Fwd
Foldable.foldr foldableFwd f i ε = i
Foldable.foldr foldableFwd f i (x :> l) = f x (Foldable.foldr foldableFwd f i l)

ftvSuffix : FTV Suffix
ftvSuffix = ftv foldableFwd ftvTyEntry

{-# TERMINATING #-}
unify : Type → Type → Contextual ⊤
solve : TyName → Suffix → Type → Contextual ⊤

unify (τ₀ ▹ τ₁) (u₀ ▹ u₁) = (unify τ₀ u₀) >> (unify τ₁ u₁)
unify (V α) (V β) = onTop (
   λ {(γ := d) →
     case ((γ ≡ᵇ α) ,′ (γ ≡ᵇ β) ,′ d) of λ where
           (false , false , _     ) → unify (V α) (V β) >> restore
           (false , true  , type τ) → unify (V α)  τ    >> restore
           (true  , false , type τ) → unify (V β)  τ    >> restore           
           (false , true  , ⁇     ) → replace ((β := type (V α)) :> ε)
           (true  , false , ⁇     ) → replace ((α := type (V β)) :> ε)
           (true  , true  , _     ) → restore
     })
unify (V α) (τ ▹ τ′) = solve α ε (τ ▹ τ′)
unify (τ ▹ τ′) (V α) = solve α ε (τ ▹ τ′)

_∈′_ = (_∈_ ftvType)
_∈″_ = (_∈_ ftvSuffix)

solve α Ξ τ = onTop (
  λ { (γ := d) → let occurs = (γ ∈′ τ) ∨ (γ ∈″ Ξ) in
    case ((γ ≡ᵇ α) ,′ occurs ,′ d) of λ where
      (false , false , _     ) → solve α Ξ τ >> restore
      (false , true  , _     ) → solve α ((γ := d) :> Ξ) τ >> replace ε
      (true  , false , type u) → modifyContext (_<>< Ξ) >> unify u τ >> restore
      (true  , false , ⁇     ) → replace (Ξ ⊗ ((α := type τ) :> ε))
      (true  , true  , _     ) → λ _ → nothing
  })

{-
  Lets test the unification now 
  ... bit late considering i've just hammered down hundreds of lines of code
-}

one : Type
one = V 0         ▹ V 2

two : Type
two = (V 1 ▹ V 1) ▹ V 1


-- to test create a context with three fresh type variable (0 - 2)
init-ctx : (TyName × Context)
init-ctx with  (fresh ⁇ >> fresh ⁇ >> fresh ⁇) (0 , ε) 
... | just (_ , s)  = s
... | nothing       = (0 , ε)

-- just to make manually checking things easier
retreiveContext : ∀ {A B} → Maybe (A × B × Context) → Context
retreiveContext (just (_ , _ , c)) = c
retreiveContext nothing            = ε
    
x = (retreiveContext ∘ unify one two) init-ctx


