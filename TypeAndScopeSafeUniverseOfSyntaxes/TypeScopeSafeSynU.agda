module TypeScopeSafeSynU where

open import Data.List
open import Data.Unit

variable
  A : Set
  B : Set
  I : Set
  σ : I
  τ : I
  li : List I

{-
  First we define what is needed to work in a 'scoped' setting.

  A scoped setting is just something where we have type/sort/kinds for ever variable
  that is in scope (whither or not we use it). So have a type of I -scoped just defines
  what it means to work in a setting where we have a bunch of variables in scope (where
  we are using I to represent types).

  Thus something which is I -scoped is something that is defined in terms of some I
  and List I (types and a list of the type of everything in scope)
-}

_-scoped : Set → Set₁
I -scoped = I → List I → Set

{-
  Now we define a bunch of combinators.

  These are operating in terms of indexed families again, in practice, we use List I as
  our index, but we define the more generally for an index A we chose.

  The reason we provide these combinators is so that we may build up a language for 
  silently passing scopes around. We can talk in terms of ⇒ ⊢ const, which are all functions
  which take in an index, we chain thse togther as necessary, then at the end we quantify
  over them with ∀[ _ ]
-}

-- Lift the function space to functions between
-- indexed families (that may later take the index)
_⇒_ : (P Q : A → Set) → (A → Set)
(P ⇒ Q) x = P x → Q x

infixr 10 _⇒_

-- some adjustment of an index
-- (in practice, an extension)
_⊢_ : (A → B) → (B → Set) → (A → Set)
(f ⊢ P) x = P (f x)

-- embed any set as a 'constant' indexed family
const : Set → (A → Set)
const P x = P

-- the type that quantifies over a predicate
∀[_] : (A → Set) → Set
∀[ P ] = ∀ {x} → P x

{-
In all the cases above, we generalize over an x, in practice, this x is a List containing
the sorts/kinds/types of all variables in scope.

So anything that is I -scoped, is anything that operates within the context of a bunch of
"in scope" variables. What that means is that if something is I -scoped, then it is of a form
that first takes and I and a List I before doing any work, where the I is whatever type we
want to use to represent types/kinds/sets and List I is the type of all the 'in scope' variables.
-}


{-
We can now supply this type 'Var' which is the type of well scoped, well sorted de Bruijn indices.

z = zero     , refers to the nearest binder
s = successor, if we know σ is a well scoped variable in x, then we know it is well scoped in τ ∷ x
               (i.e. adding things to the scope can't take something out of scope)

Now we can use these de Bruijn indices as variables safe in the knowledge that we can only ever
refer to things in scope. "Correct by construction"
-}
data Var : I -scoped where
  z : ∀[ (σ ∷_) ⊢ Var σ ]
--z : ∀ {x} → (Var σ (σ ∷ x))
  s : ∀[ Var σ ⇒ (τ ∷_) ⊢ Var σ ]
--s : ∀ {x} → Var σ x → Var σ (τ ∷ x)

{-
The reason for all this malarky is to give us a tool for talking about variables that we can use
in any syntax we choose.

For example, take the case study of STLC, we create a datatype to represent our types, then we
can define our syntax of STLC
-}

data Type : Set where
  α    : Type
  _′→_ : Type → Type → Type

data Lam : Type -scoped where
  var : ∀[ Var σ ⇒ Lam σ ]
  abs : ∀[ ((σ ∷_) ⊢ Lam τ) ⇒ Lam (σ ′→ τ) ]
  app : ∀[ Lam (σ ′→ τ) ⇒ Lam σ ⇒ Lam τ ]

-- this denotes an instrinsically typed lambda calculus. We are unable to produce bad terms:

term : Lam ((σ ′→ τ) ′→ (σ ′→ τ)) [] -- note that we start with the 'empty scope'
term = abs (abs (app (var (s z)) (var (z))))    -- this type checks in agda (λf.λx.f x)
--term = abs (abs (app (var (z)) (var (s z)))) -- this does not

