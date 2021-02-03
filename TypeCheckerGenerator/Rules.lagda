\section{Premises}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Rules where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Thinning using (_⊑_; ι; _++_)
open import Pattern using (Pattern; svar; bind; _∙; ∙_; place; ⋆; _∙_;
                           `; _-Env; match; _-_; _⊗_; _⊗svar_)
open import Expression using (Expr; _⊗expr_)
open import Data.Product using (_×_; _,_; proj₁; Σ-syntax)
open import Data.List using (List)
open import Data.String using (String)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Maybe using (Maybe; just; _>>=_)
open import Relation.Binary.PropositionalEquality using (cong; sym;
                                                         _≡_; refl)
\end{code}
}

\hide{
\begin{code}
private
  variable
    δ   : Scope
    δ'  : Scope
    γ   : Scope
    p   : Pattern δ
    p'  : Pattern γ
    pᵍ  : Pattern γ
    p`  : Pattern (suc γ)
    q`` : Pattern δ
    q   : Pattern δ
    q'  : Pattern δ
    p₂  : Pattern γ
    q₁` : Pattern γ
    p₂` : Pattern γ
\end{code}
}

A key concept we will use when defining rules is that of a premise. We use
premise in order to accumulate trust in some pattern, potentially discharging
a place in the pattern. For our premise, $p$ is some pattern that identifies places
that we already trust while $q$ is the pattern of untrusted places. The premise
establishes trust in some $p'$ and shows what remains untrusted with $q'$.

The general form is to pick a place in q, identifying how it is that we trust it
(via the data constructor used) and say that we have fresh trust in this place and so
we give back q with this place removed (by replacing the place with a trivial atom).
This is not the case for every premise as we also include premise that discharge no
untrusted place from q such as equivalence and universe checks while also providing
a constructor allowing us to represent a premise in an extended context. Regardless
it is useful to think of a premise as an entity who's role is trust establishment.

In the definition of formal rules, we do not have the luxury of referring to arbitrary
free variables and will give a chain of premises where the patterns are defined
in the empty scope (unless we have ducked under the $\vdash$ premise). We will later
require the ability to open such premises when using them to establish trust in
an arbitrary scope and so we define such an opening function $⊗premise$, the type
is also given here.

\begin{code}
data Prem  (p : Pattern δ) (q : Pattern δ) (γ : Scope) :
           (p' : Pattern γ) → (q' : Pattern δ) → Set where
   type     : (ξ : svar q δ') → (θ : δ' ⊑ γ) → Prem p q γ (place θ) (q - ξ)
   _∋'_[_]  : (T : Expr p const γ) → (ξ : svar q δ') → (θ : δ' ⊑ γ)  → Prem p q γ (place θ) (q - ξ)
   _≡'_     : Expr p const γ → Expr p const γ → Prem p q γ (` "⊤") q
   univ     : Expr p const γ → Prem p q γ (` "⊤") q
   _⊢'_     : Expr p const γ → Prem p q (suc γ) p` q`` → Prem p q γ (bind p`) q``

⊗premise : (δ : Scope) →
           Prem p q γ p' q' →
           Prem (δ ⊗ p) (δ ⊗ q) (δ + γ) (δ ⊗ p') (δ ⊗ q')
\end{code}
\hide{
\begin{code}
helper : ∀ {δ'} (δ : Scope) → (q : Pattern γ) → (ξ : svar q δ') → (δ ⊗ q) - (δ ⊗svar ξ) ≡ δ ⊗ (q - ξ)
helper δ (s ∙ t)  (ξ ∙)     = cong (λ x → Pattern._∙_ x (δ ⊗ t)) (helper δ s ξ) 
helper δ (s ∙ t) (∙ ξ)      = cong (Pattern._∙_ (δ ⊗ s)) (helper δ t ξ)
helper δ (bind q) (bind ξ)  = cong bind (helper δ q ξ)
helper δ (place x) ⋆        = refl

⊗premise {q = q} δ (type ξ θ)     rewrite sym (helper δ q ξ) = type (δ ⊗svar ξ) (ι ++ θ)
⊗premise {q = q} δ (T ∋' ξ [ θ ]) rewrite sym (helper δ q ξ) = (δ ⊗expr T) ∋' δ ⊗svar ξ [ ι ++ θ ]
⊗premise δ (x ≡' x₁)      = (δ ⊗expr x) ≡' (δ ⊗expr x₁)
⊗premise δ (univ x)       = univ (δ ⊗expr x)
⊗premise δ (_⊢'_ {p` = p`} x prem) = (δ ⊗expr x) ⊢' ⊗premise δ prem
\end{code}
}
Before we define how we might chain premise together, it is important to address
placelessness in patterns. \hl{MOVE TO PATTERNS THEN YA GOOSE!}

We define a type that is structurally equivalent to patterns except for the
absence of places. This type is indexed by patterns where we use the index
to match the structure of a Placeless and its Pattern and so it is only
possible for a Placeless to represent a placeless pattern.

We then define the removal of all places from a pattern by recursing
structurally, and replacing all places with the trivial atom ` '⊤'.

Finally we show that for any pattern $p$ we can create some Placeless indexed
by $p -places$ and, as with many of our types, define opening on Placeless.

\begin{code}
data _Placeless {γ : Scope} : Pattern γ → Set where
  `     : (s : String) → ` s Placeless
  _∙_   : {l r : Pattern γ} → (l Placeless) → (r Placeless) → (l ∙ r) Placeless
  bind  : {t : Pattern (suc γ)} → (t Placeless) → (bind t) Placeless

_-places : Pattern γ → Pattern γ
--...
place x  -places = ` "⊤"
--...
\end{code}
\hide{
\begin{code}
` x      -places = ` x
(s ∙ t)  -places = (s -places) ∙ (t -places)
bind t   -places = bind (t -places)
\end{code}
}
\begin{code}
_placeless : (p : Pattern γ) → (p -places) Placeless

_⊗pl_ : p' Placeless → (δ : Scope) → (δ ⊗ p') Placeless
\end{code}

\hide{
\begin{code}

` x placeless      = ` x
(s ∙ t) placeless  = (s placeless) ∙ (t placeless)
bind p placeless   = bind (p placeless)
place x placeless  = ` "⊤"


` c     ⊗pl δ = ` c
(s ∙ t) ⊗pl δ = (s ⊗pl δ) ∙ (t ⊗pl δ)
bind t  ⊗pl δ = bind (t ⊗pl δ)
\end{code}
}

We now use these concepts to define a chain of premise that is guaranteed to
establish complete trust in some pattern.

We may string together premises, threading what is left to trust
after each premises into what is still to trust in the next. A premise may
establish whatever trust it does, and it \emph{asks} the rest of the chain
to estrablish trust in the rest. We collect everything that we learn to
trust along the way, allowing later premise to refer to entities whose
trust was established by earlier premises.

If we wish to end a chain of premise, we must show that there is nothing left
that requires the establishment of trust by proving that the pattern the
previous premise has asked us to trust contains no places.
\begin{code}
data Prems (p₀ : Pattern γ) (q₀ : Pattern γ) : (p₂ : Pattern γ) → Set where
  ε    :  (q₀ Placeless) → Prems p₀ q₀ p₀
  _⇉_  :  Prem p₀ q₀ γ pᵍ q₁` →
          Prems (p₀ ∙ pᵍ) q₁` p₂` →
          Prems p₀ q₀ p₂`

⊗premises : (δ : Scope) → Prems p q p₂ → Prems (δ ⊗ p) (δ ⊗ q) (δ ⊗ p₂)
\end{code}
\hide{
\begin{code}
infixr 20 _⇉_
⊗premises δ (ε x)           = ε (x ⊗pl δ)
⊗premises δ (prem ⇉ prems)  = ⊗premise δ prem ⇉ ⊗premises δ prems
\end{code}}
\section{Typing Rules}

Now we will define the various rules that may be used to build typing
rules when detailing a specification.

A TypeRule is used to establish the conditions under which a piece
of syntax is determined a type. The rule applies to a subject and
must contain a premise chain which establishes complete trust in
this subject from no prior trusted knowledge. Attempting to match
a type rule is just attempting to match the subject pattern.

\begin{code}
record TypeRule : Set where
  field
    subject   : Pattern 0
    premises  : Σ[ p' ∈ Pattern 0 ] Prems (` "⊤") subject p'
open TypeRule

match-typerule : (rule : TypeRule)  →
                 Term const γ       →
                 Maybe ((γ ⊗ (subject rule)) -Env)
match-typerule rule term = match term (subject rule)
\end{code}

The Universe rule work in much the same way except that the premise
chain seeks to establish trust in a trivial placeless pattern. I.e.
it seeks to establish no trust whatsever since the Universe rule
applies to an input and we take inputs to be entites which we trust.
Matching a Universe rule involves matching the input only.

\hide{
\begin{code}
record UnivRule : Set where
  field
    input     :  Pattern 0
    premises  :  Σ[ p' ∈ Pattern 0 ] Prems input (` "⊤") p'
open UnivRule

match-univrule  :  (rule : UnivRule)  →
                   Term const γ       →
                   Maybe ((γ ⊗ (input rule)) -Env)
match-univrule rule term = match term (input rule)
\end{code}}

The Type-Checking rule (∋) involves both an input and a subject. For
$T ∋ t$ we take T to be a trusted input and seek to establish trust
in t. Our premise chain reflects this by using the input as its
trusted pattern and seeking trust in the subject. Matching occurs on
both the input and the subject and so, if successful, returns a
pair of environments.

\begin{code}
record ∋rule : Set where
  field
    subject  : Pattern 0
    input    : Pattern 0
    premises : Σ[ p' ∈ Pattern 0 ] Prems input subject p'
open ∋rule

match-∋rule  :  (rule : ∋rule)  →
                Term const γ    →
                Term const γ    →
                  (Maybe
                    (((γ ⊗ (input rule))   -Env)
                         ×
                    ((γ ⊗ (subject rule))  -Env)))
match-∋rule rule Tterm tterm
  = do
      inenv   ←  match Tterm (input rule)
      subenv  ←  match tterm (subject rule)
      just (inenv , subenv)
\end{code}

Our rules for elimination work slightly differently from those which operate on
constructions above. Eliminations use some \emph{eliminator} in order to eliminate
some \emph{target}. An elimination rule, if it matches, is used in order to try
and \emph{supply} us with the type resulting from the elimination.

In order to build the output, it is not necessary for us to hold any description
of the target term whatsoever, it is enough that we describe what type we require
it to be. In theoretical literature, elimination rules for constructs take a
certain form.

\begin{center}
\begin{prooftree}
      \hypo{target ∈ T}
      \hypo{\ldots}
      \infer2[elim]{target \; eliminator ∈ S}
\end{prooftree}
\end{center}

We do not need the user to supply this information and so we take just a pattern
that we might use to match against $T$, one that we might match against $eliminator$,
and seek to establish trust in $eliminator$ under the assumption that we trust $T$.
We also use an Expression to build the type of the elimination from everything in
which the premise chain has established trust.

\begin{code}
record ElimRule : Set where
  field
    targetPat   :  Pattern 0
    eliminator  :  Pattern 0
    premises    :  Σ[ p' ∈ Pattern 0 ] Prems targetPat eliminator p'
    output      :  Expr (proj₁ premises) const 0

match-erule : (rule : ElimRule)   →
              (T : Term const γ)  →
              (s : Term const γ)  →
              Maybe
                (((γ ⊗ (ElimRule.targetPat rule)) -Env)
                     ×
                ((γ ⊗ (ElimRule.eliminator rule)) -Env))
match-erule rule T s = do
                         T-env ← match T (targetPat rule)
                         s-env ← match s (eliminator rule)
                         just (T-env , s-env)
                       where
                         open ElimRule
\end{code}
