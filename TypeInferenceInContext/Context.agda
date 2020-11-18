module Context where

open import Data.Unit
open import Data.Nat using (suc)
open import Data.Bool
open import Data.Product
open import Function using (_∘_; case_of_)
open import Lists
open import Types
open FTV
import Monads
open Monads.StateMaybe
open Monads.Maybe using (Maybe; just; nothing)

{-
  We can either declare types with an actual type
  or without giving them a 'type value' i.e. we are
  bringing a new type variable into scope but making
  no assumptions about what it might be
-}
data TyDecl : Set where
  type : Type → TyDecl
  ⁇    : TyDecl

{-
  An entry in the context is a binding from a type variable
  to a declaration
-}
data TyEntry : Set where
  _:=_ : TyName → TyDecl → TyEntry

{-
  We can check whither a free variable exists in an entry
-}
ftvTyEntry : FTV TyEntry
(ftvTyEntry ∈ α) (_ := type x) =
  let _∈_ = _∈_ ftvType in
    α ∈ x
(ftvTyEntry ∈ α) (_ := ⁇)      = false

data Entry : Set where
  TY : TyEntry → Entry
  ⋯  : Entry

Context = Bwd Entry
Suffix  = Fwd TyEntry

_<><_ : Context → Suffix → Context
Γ <>< ε        = Γ
Γ <>< ((α := d) :> Ξ) = (Γ :< TY (α := d)) <>< Ξ

{-
  Now we look at the context manipulation monad
-}

-- state always holds the 'next variable to use'
-- along with the context
Contextual = StateMaybe (TyName × Context)

fresh : TyDecl → Contextual TyName
fresh d = 
  do
    (β , Γ) ← get
    put (suc β , (Γ :< TY (β := d)))
    return β

getContext : Contextual Context
getContext s = just ((proj₂ s) , s)

putContext : Context → Contextual ⊤
putContext Γ = 
  do
    β ← λ s → just (proj₁ s , s)
    put (β , Γ)

modifyContext : (Context → Context) → Contextual ⊤
modifyContext f = getContext >>= (putContext ∘ f)

{-
  Processing the context
-}

data Extension : Set where
  Restore : Extension
  Replace : Suffix → Extension

{-# TERMINATING #-}
onTop : (TyEntry → Contextual Extension) → Contextual ⊤
onTop f = 
  do
    Γ :< vD ← getContext where _ → λ _ → nothing
    putContext Γ
    case vD of λ where
      (TY αD) → do
                 m ← f αD
                 case m of λ where
                   Restore     → modifyContext (_:< vD)
                   (Replace Ξ) → modifyContext (_<>< Ξ)
      -- if the top entry isn't a type entry, recurse, but remember
      -- to stick the top entry back on when you're finished!
      _       → onTop f >> modifyContext (_:< vD)

restore : Contextual Extension
restore = return Restore

replace : Suffix → Contextual Extension
replace = return ∘ Replace

