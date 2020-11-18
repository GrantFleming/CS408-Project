module SynU where

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst

record One : Set where
  constructor <>

data Bwd (X : Set) : Set where
  []   : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

data Desc (X : Set) -- the set of sorts of terms
  : Set1 where
  term : X -> Desc X
  pair : Desc X -> Desc X -> Desc X
  unit : Desc X
  tag  : (T : Set) -> (T -> Desc X) -> Desc X
  bind : X -> Desc X -> Desc X

[_] : forall {X} -> Desc X -> (X -> Bwd X -> Set) -> Bwd X -> Set
[ term x ] R G = R x G
[ pair D D' ] R G = [ D ] R G >< \ _ -> [ D' ] R G
[ unit ] R G = One
[ tag T D ] R G = T >< \ t -> [ D t ] R G
[ bind x D ] R G = [ D ] R (G -, x)

data Var {X : Set}(x : X) : Bwd X -> Set where
  ze : forall {G} -> Var x (G -, x)
  su : forall {G y} -> Var x G -> Var x (G -, y)

data Term {X : Set}(F : X -> Desc X)(x : X)(G : Bwd X) : Set where
  var : Var x G -> Term F x G
  con : [ F x ] (Term F) G -> Term F x G

data Ty : Set where
  base : Ty
  _>>_ : Ty -> Ty -> Ty  

data LorA : Set where lam app : LorA

data Zero : Set where

HELP : Ty -> Desc Ty
HELP base = tag Zero \ ()
HELP (S >> T) = bind S (term T)

STLC : Ty -> Desc Ty
STLC T = tag LorA \
  { lam -> HELP T
  ; app -> tag Ty \ S -> pair (term (S >> T)) (term S) 
  }

Tm : Bwd Ty -> Ty -> Set
Tm G T = Term STLC T G

fun : forall {G S T} -> Tm (G -, S) T -> Tm G (S >> T)
fun body = con (lam , body)

apply : forall {G S T} -> Tm G (S >> T) -> Tm G S -> Tm G T
apply f s = con (app , (_ , (f , s)))
