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
                           thing; `; ⊥; _-Env; match; _-_; _⊗_; _⊗svar_)
open import Expression using (Expr; _⊗expr_; toTerm; `)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.List using (List)
open import Data.String using (String)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Maybe using (Maybe; just; _>>=_)
open import Relation.Binary.PropositionalEquality using (cong; sym;
                                                         _≡_; refl; subst; _≢_)
\end{code}
}

\hide{
\begin{code}
private
  variable
    δ   : Scope
    δ'  : Scope
    γ   : Scope
    γ'  : Scope
    l   : Scope
    p   : Pattern δ
    p'  : Pattern γ
    pᵍ  : Pattern γ
    p`  : Pattern (suc γ)
    q`` : Pattern δ
    q   : Pattern δ
    q'  : Pattern δ
    q`  : Pattern δ
    p₂  : Pattern γ
    q₁` : Pattern γ
    p₂` : Pattern γ
    qᵍ  : Pattern γ
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
Ty
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
⊗eqiv : ∀ {δ'} (δ : Scope) → (q : Pattern γ) → (ξ : svar q δ') → (δ ⊗ q) - (δ ⊗svar ξ) ≡ δ ⊗ (q - ξ)
⊗eqiv δ (s ∙ t)  (ξ ∙)     = cong (λ x → Pattern._∙_ x (δ ⊗ t)) (⊗eqiv δ s ξ) 
⊗eqiv δ (s ∙ t) (∙ ξ)      = cong (Pattern._∙_ (δ ⊗ s)) (⊗eqiv δ t ξ)
⊗eqiv δ (bind q) (bind ξ)  = cong bind (⊗eqiv δ q ξ)
⊗eqiv δ (place x) ⋆        = refl

⊗premise {q = q} δ (type ξ θ)     rewrite sym (⊗eqiv δ q ξ) = type (δ ⊗svar ξ) (ι ++ θ)
⊗premise {q = q} δ (T ∋' ξ [ θ ]) rewrite sym (⊗eqiv δ q ξ) = (δ ⊗expr T) ∋' δ ⊗svar ξ [ ι ++ θ ]
⊗premise δ (x ≡' x₁)      = (δ ⊗expr x) ≡' (δ ⊗expr x₁)
⊗premise δ (univ x)       = univ (δ ⊗expr x)
⊗premise δ (_⊢'_ {p` = p`} x prem) = (δ ⊗expr x) ⊢' ⊗premise δ prem
\end{code}
}

We must now define a type that is structurally equivalent to patterns except
for the absence of places. This type is indexed by the pattern that we are
trying to represent. It is only possible to represent placeless patterns with
this type. We write various mechanics using this new type that we will not detail
here, including the ability to remove a place from a pattern given an svar, and
thus for any pattern $p$ we have the ability to create some $(p\;-places) Placeless$.
Placeless can be opened just as Patterns can be.

\begin{code}
data _Placeless {γ : Scope} : Pattern γ → Set where
  `     : (s : String) → ` s Placeless
  _∙_   : {l r : Pattern γ} → (l Placeless) → (r Placeless) → (l ∙ r) Placeless
  bind  : {t : Pattern (suc γ)} → (t Placeless) → (bind t) Placeless
  ⊥     : ⊥ Placeless
\end{code}
\hide{
\begin{code}
_-places : Pattern γ → Pattern γ
place x  -places = ` "⊤"
` x      -places = ` x
(s ∙ t)  -places = (s -places) ∙ (t -places)
bind t   -places = bind (t -places)
⊥        -places = ⊥
\end{code}
}
\hide{
\begin{code}
_placeless : (p : Pattern γ) → (p -places) Placeless
` x placeless      = ` x
(s ∙ t) placeless  = (s placeless) ∙ (t placeless)
bind p placeless   = bind (p placeless)
place x placeless  = ` "⊤"
⊥ placeless        = ⊥

_⊗pl_ : p' Placeless → (δ : Scope) → (δ ⊗ p') Placeless
` c     ⊗pl δ = ` c
(s ∙ t) ⊗pl δ = (s ⊗pl δ) ∙ (t ⊗pl δ)
bind t  ⊗pl δ = bind (t ⊗pl δ)
⊥       ⊗pl δ = ⊥
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

Now we will define the various types that represent typing rules that
might exist in some type checker.

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
\end{code}
\hide{
\begin{code}
match-typerule : (rule : TypeRule)  →
                 Term const γ       →
                 Maybe ((γ ⊗ (TypeRule.subject rule)) -Env)
match-typerule rule term = match term (TypeRule.subject rule)
\end{code}
}
The Universe rule work in much the same way except that the premise
chain seeks to establish trust in a trivial placeless pattern. I.e.
it seeks to establish no trust whatsever since the Universe rule
applies to an input and we take inputs to be entites which we trust.
Matching a Universe rule involves matching the input only.
\begin{code}
record UnivRule : Set where
  field
    input     :  Pattern 0
    premises  :  Σ[ p' ∈ Pattern 0 ] Prems input (` "⊤") p'
\end{code}
\hide{
\begin{code}
match-univrule  :  (rule : UnivRule)  →
                   Term const γ       →
                   Maybe ((γ ⊗ (UnivRule.input rule)) -Env)
match-univrule rule term = match term (UnivRule.input rule)
\end{code}
}
\hide{
\begin{code}
open import Data.Bool using (Bool; true; false)
open import Data.Empty renaming (⊥ to bot)
open import Relation.Nullary using (¬_; Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Thinning using (_O)
open import Data.Nat using (_≟_)
open import Pattern using (_‼_; _-penv_; svar-builder; X; _∙; ∙_; bind; bind-count-bl; build)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)

_is_ : (v : svar p γ) → (ξ : svar p γ) → Dec (v ≡ ξ)
⋆ is ⋆ = yes refl
(v ∙) is (ξ ∙) with v is ξ
... | yes p = yes (cong _∙ p)
... | no ¬p = no λ { refl → ¬p refl}
(v ∙) is (∙ ξ) = no λ ()
(∙ v) is (ξ ∙) = no λ ()
(∙ v) is (∙ ξ) with v is ξ
... | yes p = yes (cong ∙_ p)
... | no ¬p = no (λ { refl → ¬p refl })
bind v is bind ξ with v is ξ
... | yes p = yes (cong bind p)
... | no ¬p = no (λ { refl → ¬p refl})

-svar : (v : svar p γ) → (ξ : svar p δ) →
          γ ≢ δ ⊎ Σ[ eq ∈ γ ≡ δ ] subst (svar p) eq v ≢ ξ
          → svar (p - ξ) γ
-svar ⋆ ⋆ (inj₁ x) = ⊥-elim (x refl)
-svar ⋆ ⋆ (inj₂ (refl , neq)) = ⊥-elim (neq refl)
-svar (v ∙) (ξ ∙) (inj₁ x) = (-svar v ξ (inj₁ x)) ∙
-svar (v ∙) (ξ ∙) (inj₂ (refl , neq)) = (-svar v ξ (inj₂ (refl , neq ∘ (cong _∙)))) ∙
-svar (v ∙)    (∙ ξ)    eqs = v ∙
-svar (∙ v)    (ξ ∙)    eqs = ∙ v
-svar (∙ v) (∙ ξ) (inj₁ x) = ∙ -svar v ξ (inj₁ x)
-svar (∙ v) (∙ ξ) (inj₂ (refl , neq)) = ∙ -svar v ξ (inj₂ (refl , neq ∘ cong (∙_)))
-svar (bind v) (bind ξ) (inj₁ x) = bind (-svar v ξ (inj₁ x))
-svar (bind v) (bind ξ) (inj₂ (refl , neq)) = bind (-svar v ξ (inj₂ (refl , neq ∘ cong bind)))

binds : ∀ {γ} → (n : ℕ) → Pattern (n + γ) → Pattern γ
binds zero p = p
binds (suc n) p = bind (binds n p)

bindsT : ∀ {γ} → (n : ℕ) → Const (n + γ) → Const γ
bindsT zero t = t
bindsT (suc n) t = bind (bindsT n t)

-- why can't the last -Env work out γ by itself
bindsenv : ∀ {n}{p : Pattern (n + γ)} → p -Env →  _-Env {γ = γ} (binds n p)
bindsenv {n = zero} env  = env
bindsenv {n = suc n} env = bind (bindsenv {n = n} env)

proof : ∀ {n γ : Scope}{p : Pattern (suc (n + γ))} → binds {γ} n (bind p) ≡ bind (binds n p)
proof {n = zero}  = refl
proof {n = suc n} = cong bind proof

bind-count : svar p δ → ℕ
bind-count ⋆ = 0
bind-count (v ∙) = bind-count v
bind-count (∙ v) = bind-count v
bind-count (bind v) = suc (bind-count v)

lem5 : ∀{θ : δ' ⊑ γ'}{v : svar-builder p (place θ)} → bind-count-bl v ≡ bind-count (build v)
lem5 {v = X} = refl
lem5 {v = v ∙} = lem5 {v = v}
lem5 {v = ∙ v} = lem5 {v = v}
lem5 {v = bind v} = cong suc (lem5 {v = v})
{-# REWRITE lem5 #-}

proof' : ∀(v : svar p γ)(ξ : svar p δ)(pr) → bind-count v ≡ bind-count (-svar v ξ pr)
proof' (⋆     )  (⋆     )  (inj₁ x) = ⊥-elim (x refl)
proof' (⋆     )  (⋆     )  (inj₂ (refl , neq)) = ⊥-elim (neq refl)
proof' (v ∙   )  (ξ ∙   )  (inj₁ x) = proof' v ξ (inj₁ x)
proof' (v ∙) (ξ ∙) (inj₂ (refl , snd)) = proof' v ξ (inj₂ (refl , λ x → snd (cong _∙ x)))
proof' (v ∙   )  (∙ ξ   )  pr      = refl
proof' (∙ v   )  (ξ ∙   )  pr  = refl
proof' (∙ v) (∙ ξ) (inj₁ x) = proof' v ξ (inj₁ x)
proof' (∙ v) (∙ ξ) (inj₂ (refl , snd)) = proof' v ξ (inj₂ (_ , λ x → snd (cong ∙_ x)))
proof' (bind v) (bind ξ) (inj₁ x) = cong suc (proof' v ξ (inj₁ x))
proof' (bind v) (bind ξ) (inj₂ (refl , snd)) = cong suc (proof' v ξ (inj₂ (refl , (λ x → snd (cong bind x)))))
\end{code}
}
The Type-Checking rule (∋) involves both an input and a subject. For
$T ∋ t$ we take T to be a trusted input and seek to establish trust
in t. Our premise chain reflects this by using the input as its
trusted pattern and seeking trust in the subject. Matching occurs on
both the input and the subject and , if successful, returns a
pair of environments. We may also use this rule to reverse engineer
the type of any place in the subject, taking advantage of the fact that
our premise chain can only establish trust in a place by ultimately making
a statement either about its type, or about it being a type. This function
turned out to be non-trivial, and many proofs were required to convice
Agda to accept the implementation. An alternative might have been to
construct a pattern environment where each place corresponded to the
type of the corresponding part of the pattern. We could have even gone
so far as to generalise what may be stored at places in patterns and
teased out some applicative structure.
\begin{code}
record ∋rule : Set where
  field
    subject  : Pattern 0
    input    : Pattern 0
    premises : Σ[ p' ∈ Pattern 0 ] Prems input subject p'
open ∋rule

typeOf : (r : ∋rule)                   →
         (s : svar (γ ⊗ subject r) δ)  →
         (γ ⊗ input r) -Env            →
         ((γ ⊗ (subject r))  -Env)     →
         Const ((bind-count s) + γ)
\end{code}
\hide{
\begin{code}
typeOf {γ = γ'} r v ienv senv =  helper v ienv senv (⊗premises γ' (proj₂ (premises r)))
  where
    lem : ∀ {n}{δ'}{p q q' p'' : Pattern δ}{p' : Pattern (n + δ)} →
          (s : svar q δ') → p -Env → q -Env → Prem p q (n + δ) p' q'  → Prems (p ∙ (binds n p')) q' p'' → Const ((bind-count s) + δ)
          
    helper : ∀ {δ'}{p q p' : Pattern δ} → (s : svar q δ') → p -Env → q -Env → Prems p q p' → Const ((bind-count s) + δ)

    lem {δ' = δ''} v env qenv (type {δ' = δ'} ξ θ) prems with δ'' ≟ δ'
    ... | no ¬p rewrite proof' v ξ (inj₁ ¬p) = helper (-svar v ξ (inj₁ ¬p)) (env ∙ bindsenv (thing (ξ ‼ qenv))) (qenv -penv ξ) prems 
    ... | yes refl  with v is ξ
    ... | no ¬p rewrite proof' v ξ (inj₂ (refl , ¬p)) = helper (-svar v ξ (inj₂ (refl , ¬p))) (env ∙ bindsenv (thing (ξ ‼ qenv))) (qenv -penv ξ) prems
    ... | yes p = ` "Type"
    lem {n = n} {δ' = δ''} {p' = place ϕ} v env qenv prem@(_∋'_[_] {δ' = δ'} T ξ θ) prems with δ'' ≟ δ'
    ... | no ¬p rewrite proof' v ξ (inj₁ ¬p) = helper (-svar v ξ (inj₁ ¬p)) (env ∙ bindsenv (thing (ξ ‼ qenv))) (qenv -penv ξ) prems
    ... | yes refl with v is ξ | n ≟ (bind-count ξ)
    ... | no ¬p | _ rewrite proof' v ξ (inj₂ (refl , ¬p)) = helper (-svar v ξ (inj₂ (refl , ¬p))) (env ∙ bindsenv (thing (ξ ‼ qenv))) (qenv -penv ξ) prems
    ... | yes refl | no _  = ` "unknown"
    ... | yes refl | yes refl = toTerm env T
    lem v env qenv (x ≡' x₁) prems  = helper v (env ∙ bindsenv `) qenv prems
    lem v env qenv (univ x) prems   = helper v (env ∙ bindsenv `) qenv prems
    lem {δ = δ} {n = n} {p = p} {q' = q'} {p'' = p''} v env qenv (_⊢'_ {p` = p`} x prem) prems
      rewrite proof {n = n} {γ = δ} {p = p`}
      = lem v env qenv prem prems
    helper v env qenv (ε x) = ⊥-elim (lm v x)
      where
        lm : svar p γ → p Placeless → bot
        lm ⋆ ()
        lm (v ∙) (l ∙ _) = lm v l
        lm (∙ v) (_ ∙ r) = lm v r
        lm (bind v) (bind t) = lm v t
    helper v env qenv (p ⇉ prems) = lem v env qenv p prems

  
match-∋rule  :  (rule : ∋rule)  →
                (type term : Term const γ) →
                (Maybe
                  (((γ ⊗ (input rule))   -Env)
                       ×
                   ((γ ⊗ (subject rule))  -Env)))
match-∋rule rule ty tm
  = do
      tyenv   ←  match ty (input rule)
      tmenv  ←  match tm (subject rule)
      just (tyenv , tmenv)
\end{code}
}

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
which the premise chain has established trust. Matching an elimination rule requires
matching both the target pattern and the eliminator.
\begin{code}
record ElimRule : Set where
  field
    targetPat   :  Pattern 0
    eliminator  :  Pattern 0
    premises    :  Σ[ p' ∈ Pattern 0 ] Prems targetPat eliminator p'
    output      :  Expr (proj₁ premises) const 0
open ElimRule
\end{code}
\hide{
\begin{code}
ERuleEnv : ∀{γ} → ElimRule → Set
ERuleEnv {γ} rule = ((γ ⊗ (targetPat rule)) -Env)
                        ×
                    ((γ ⊗ (eliminator rule)) -Env)

match-erule : (rule : ElimRule)   →
              (T : Term const γ)  →
              (s : Term const γ)  →
              Maybe (ERuleEnv rule)
match-erule rule T s = do
                         T-env ← match T (targetPat rule)
                         s-env ← match s (eliminator rule)
                         just (T-env , s-env)
                       where
                         open ElimRule
\end{code}
}
In this section we have glossed over the functions that were defined to match the
various rules, however these have explanitory names such as \emph{match-∋rule} which
will make them obvious if we come across them when exploring future sections of
code.
