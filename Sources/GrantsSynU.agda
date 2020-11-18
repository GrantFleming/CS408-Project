{-

Here we define a syntactic universe.

Some questions I would like to answer:
  - what is a syntactic universe

-}

module GrantsSynU where

open import Data.Product
open import Data.Unit

{-  
  To make it easier on the head, we define backward lists so that we
  can have right-to-left contexts.
-}

data Bwd (A : Set) : Set where
  ε : Bwd A
  _-,_ : Bwd A → A → Bwd A

{-

We start by creating a type that 'describes' things in our syntax.

Whatever we choose to represent the terms, we can describe them as
terms, pairs of things, uni, tag them with some more info, or a binding.

The idea (I think) is that we are not commiting to any syntax in particular,
but we are able to describe certain critical things, in any syntax we choose.

Thus we can generically define <some stuff> later to wokr over any syntax
we may choose.

-}

data Desc (X : Set) : Set₁ where
  term : X → Desc X
  pair : Desc X → Desc X → Desc X
  unit : Desc X
  tag  : (T : Set) → (T → Desc X) → Desc X
  bind : X → Desc X → Desc X

{-
  Now we look at evaluating described terms. What does this mean?
  The description of the term determins how we evaluate it.
  Again we generalise over some way of evaluating in by being passed
  in a function that evaluates terms.
-}
[_] : forall {X} → Desc X → (X → Bwd X → Set) → Bwd X → Set
[ term x ]     Ρ Γ = Ρ x Γ
[ pair D¹ D² ] Ρ Γ = [ D¹ ] Ρ Γ × [ D² ] Ρ Γ
[ unit ]       Ρ Γ = ⊤
[ tag T ⇒D ]   Ρ Γ = Σ[ t ∈ T ] [ ⇒D t ] Ρ Γ
[ bind x D ]   Ρ Γ = [ D ] Ρ (Γ -, x)
