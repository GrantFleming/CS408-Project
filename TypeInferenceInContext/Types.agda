module Types where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Bool
open import Category.Functor renaming (RawFunctor to Functor)
open import Function using (id; _∘_)
open import Fold

open Functor
open Foldable

private
  variable
    A B : Set

{-
  Types are either atomic or function types
  parameterized by whatever we want to use as
  a variable name
-}
data Ty (a : Set)  : Set where
  V   : a → Ty a
  _▹_ : Ty a → Ty a → Ty a

-- Ty is a functor
tyFunctor : Functor Ty
(tyFunctor <$> f) (V x) = V (f x)
(tyFunctor <$> f) (x₁ ▹ x₂) = 
  let _<$>_ = _<$>_ tyFunctor in
    (f <$> x₁) ▹ (f <$> x₂)

-- Ty is foldable
tyFoldable : Foldable Ty
foldr tyFoldable f i (V x)    = f x i
foldr tyFoldable f i (x ▹ x₁) =
  let foldr = foldr tyFoldable in
    foldr  f (foldr f i x₁) x

{-
  We will use the naturals as variable names therefore
  types for us are Ty indexed by naturals
-}
TyName = ℕ
Type   = Ty TyName

record FTV (a : Set) : Set where
  field
    _∈_ : TyName → a → Bool
open FTV

ftvTyName : FTV TyName
_∈_ ftvTyName = _==_


{-
  Allows us determin structures we can compute free type
  variable for recursivly. If we have a foldable structure
  full of data on which we can calculate free type variables
  then we can calculate them across the whole structure
-}
ftv : ∀ {t a} → Foldable t → FTV a → FTV (t a)
_∈_ (ftv ft ftva) α t =
  let _∈_ = _∈_ ftva in
  let foldr = foldr ft in 
    foldr (_∨_ ∘ (α ∈_)) false t

-- therefore we can make ftvTypes easily if we want
ftvType : FTV Type
ftvType = ftv tyFoldable ftvTyName
