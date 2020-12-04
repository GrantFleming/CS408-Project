{-

Here we define a syntactic universe.

-}

module GrantsSynU where

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


{-  
  To make it easier on the head, we define backward lists so that we
  can have right-to-left contexts.
-}

data Bwd (A : Set) : Set where
  ε : Bwd A
  _-,_ : Bwd A → A → Bwd A

private
  variable
    X : Set
    α : X
    σ : X
    τ : X
    Γ : Bwd X

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
  tag  : (T : Set) → (T → Desc X) → Desc X
  bind : X → Desc X → Desc X
  term : X → Desc X
  
  pair : Desc X → Desc X → Desc X
  unit : Desc X

{-
  Now we look at evaluating described terms. What does this mean?
  The description of the term determins how we evaluate it.
  Again we generalise over some way of evaluating in by being passed
  in a function that evaluates terms.
-}

⟦_⟧ : Desc X → (X → Bwd X → Set) → Bwd X → Set
⟦ tag T ⇒D ⟧   Ρ Γ = Σ[ t ∈ T ] ⟦ ⇒D t ⟧ Ρ Γ
⟦ bind x D ⟧   Ρ Γ = ⟦ D ⟧ Ρ (Γ -, x)
⟦ term x ⟧     Ρ Γ = Ρ x Γ

⟦ pair D¹ D² ⟧ Ρ Γ = ⟦ D¹ ⟧ Ρ Γ × ⟦ D² ⟧ Ρ Γ
⟦ unit ⟧       Ρ Γ = ⊤

{-
  Variables are de-bruijn indexed in a context
-}

data Var (x : X) : (Bwd X) → Set where
  ze : Var x (Γ -, x)
  su : Var x Γ → Var x (Γ -, α)

{-
  Terms are either variables, or constructions in the language.
  This data type allows us to create "term trees"

  Here, F is our way of creating constructions in the language.
-}

data Term (F : X → Desc X)(x : X)(Γ : Bwd X) : Set where
  var : Var x Γ → Term F x Γ
  con : ⟦ F x ⟧ (Term F) Γ  → Term F x Γ

{-

  Now, as an example, we will construct STLC in this universe of syntaxes
  -----------------------------------------------------------------------

  This is 'hooking up' a syntax to our description. This is the part that
  we will ultimately provide code so that we may hook up an arbitrary
  syntax of the user.

-}

-- our types are classic simple types

-- these types in the generic case come from the user. So we need
-- a way for users to define types and type constructors for all
-- types they want "baked into" the language.

-- it might be an idea to have the user list out the format of the
-- types they want separately from the typing rules for ease.
-- for instance, if there is a judgement form: xyz <- A (meaning
-- that a type A is synthesized for some term xyz) then A must correspond
-- to an actual type listed previously.

data Ty : Set where
  b   : Ty
  _⇨_ : Ty → Ty → Ty

infixr 20 _⇨_

-- we need something to 'tag' terms with so we can identify information
-- about the syntactic construct. A tag for each language construct.
-- Ultimately this could be taken from the grammar in ???
data LorA : Set where lam app : LorA

-- and this is how we build our descriptions from types. I.e. all types
-- are described in a certain way, even if there are multiple concrete values
-- that they could ultimately be.

-- the question is, how is this detemined from the user
-- so we need to provide a descriptions for each possible tag
-- since each tag corresponds to a language construct (non-terminal BNF symbol)
-- Thus after defining the BNF grammar, the user will have to list each
-- along with something that indicates a description.
STLC : Ty → Desc Ty
STLC τ = tag LorA (λ where
                     lam → helper τ
                     app → tag Ty (λ σ → pair (term (σ ⇨ τ)) (term σ)))
                     -- note we will need to provide σ
           where
           helper : Ty → Desc Ty
           helper b = tag ⊥ λ () -- cannot have a λ with the base type
           helper (σ ⇨ τ) = bind σ (term τ)

-- we can now produce the type of terms of STLC by instantiating Term above
-- with our new way of interpreting types (STLC) extending our STLC with variables
Tm : Bwd Ty → Ty → Set
Tm Γ τ = Term STLC τ Γ

-- finally, now we have our type of terms, we can provide ways of constructing
-- actual terms (functions and applications)

func : Tm (Γ -, σ) τ → Tm Γ (σ ⇨ τ)
func x = con (lam , x)

-- now we could define some actual example functions in STLC such as identity

id : Tm Γ (σ ⇨ σ)
id = con (lam , (var ze))

-- perhaps using our 'func'
id' : Tm Γ (σ ⇨ σ)
id' = func (var ze)

-- both are equivalent

_ : ∀ {Γ : Bwd Ty}{σ : Ty} → id {Γ} {σ} ≡ id'
_ = refl

-- or perhaps a term which is a λ abstraction which takes a function and an argument and applies it
appfunc : Tm Γ ((σ ⇨ τ) ⇨ σ ⇨ τ)
appfunc = con (lam , (con (lam , (con (app , (_ , ((var (su ze)) , (var ze))))))))


apply : Tm Γ (σ ⇨ τ) → Tm Γ σ → Tm Γ τ
apply f x = con (app , _ , (f , x))

-- thus an equivalent to appfunc

appfunc' : Tm Γ ((σ ⇨ τ) ⇨ σ ⇨ τ)
appfunc' = func (func (apply (var (su ze)) (var ze)))

{-

  Note that we are construcing terms according to Tm Γ <some type> - i.e. we are giving the
  type, and constructing a term of that type.

  Also note that this construction is forcing us to produce well-typed terms according
  to the type specified in advance. I.e. try swapping variables around in appfunc and
  notice that is it not an accepted value.

  This way works if we are checking types, i.e. if we want to check that some syntax
  "λf.λx.f x" has some type "(σ ⇨ τ) ⇨ σ ⇨ τ" then we can check that when we
  parse it and get "con (lam , (con (lam , (con (app , (_ , ((var (su ze)) , (var ze))))))))"
  this parsed form is a value of "Tm ? ((σ ⇨ τ) ⇨ σ ⇨ τ)"

  So .... in summary:

  The ultimate end-product will take in the source code, parse it and identify the entry-point
  then attempt to parse the entry-term to some Tm ε τ , where if it is successful, the final
  type of the checked program is τ.
-}
