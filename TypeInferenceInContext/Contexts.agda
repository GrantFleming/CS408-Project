module Contexts where

open import Data.Bool
open import Types
open FTV

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

data Context : Set where
  ε     : Context
  _<:_  : Context → TyEntry → Context

data Suffix : Set where
  ε     : Suffix
  _:>_  : TyEntry → Suffix → Suffix

_<><_ : Context → Suffix → Context
Γ <>< ε        = Γ
Γ <>< (e :> Ξ) = (Γ <: e) <>< Ξ
  
  
