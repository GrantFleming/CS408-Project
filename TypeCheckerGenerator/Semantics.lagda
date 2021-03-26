\section{Semantics}

\hide{
\begin{code}
{-# OPTIONS --rewriting #-}
module Semantics where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Pattern using (Pattern; _∙_; _⊗_; _-Env; match; termFrom)
open import Context using (Context) renaming (_,_ to _-,_)
open import Data.String using (_++_)
open import Expression using (toTerm; Con)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Failable using (Failable; succeed; fail)
open import Data.Nat using (_+_; _≟_; suc)
open import Thinning using (_⟨term_)
open import Rules using (∋rule; typeOf; bind-count; ElimRule; ERuleEnv; match-erule; Prems; ⊗premises)
open import Pattern using (`; _∙_; bind; place; thing; svar; svar-builder;
                           X; ⇚; ⇛; ↳; build; bind-count-bl)
open import Relation.Nullary using (yes; no; ¬_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (sym; subst; _≡_; refl; cong)
open ∋rule
\end{code}
}

\hide{
\begin{code}
private
  variable
    γ : Scope
    δ : Scope
    d : Dir

PremsChecker' : Scope → Set
PremsChecker' δ = {p q p' : Pattern δ} → p -Env → q -Env  → Prems p q p' → Failable (p' -Env)
\end{code}
}
When constructing our elimination typing rule, we noted that we did not
require information about the syntax of the target itself, only its type.
For $β$-reduction we now require this information and so we create a type
that wraps an elimination typing rule but provides the extra information we
need: some pattern for the target of elimination and some expression
showing how we construct the reduced term.

Matching a $β$-rule involves matching the enclosed elimination rule and the
pattern of the target, when such a rule is matched we might then appeal to
$β$-reduce. We are guaranteed to be able to return a computation here since
we have kept the required type information to hand and so we make use of the
$↞↞$ operator that we introduced in section \ref{section-corelanguage}.

\begin{code}
record β-rule : Set where
  open ElimRule
  field
    target   : Pattern 0
    erule    : ElimRule
    redTerm  : Con (target ∙ targetPat erule ∙ eliminator erule) 0
  redType  = output erule
  eprems   = proj₂ (premises erule)

  βRule-Env : {γ : Scope} → Set
  βRule-Env {γ} = (γ ⊗ target) -Env × ERuleEnv erule

  β-reduce  : βRule-Env →
              (γ ⊗ (proj₁ (premises erule))) -Env →
              Compu γ 
  β-reduce (tenv , tyenv , eenv) p'env
    = ↞↞  (toTerm (tenv ∙ tyenv ∙ eenv) redTerm)
          (toTerm p'env redType)
\end{code}
\hide{
\begin{code}
  open Data.Maybe using (_>>=_)
  β-match : (targ type elim : Const γ) → Maybe βRule-Env
  β-match tar ty el = do
                        t-env  ← match tar target
                        e-env ← match-erule erule ty el
                        just (t-env , e-env)
open β-rule        
\end{code}
}
\hide{
\begin{code}
open import Failable using (_>>=_)
\end{code}
}
We now have what is required to find a matching rule by matching the various
patterns that it may contain. We iterate over the list of rules and return the
first match. We chose a 'first match' approach here for simplicity of
implementation however it is acknowledged that other approaches are far more
suitable. We discuss this later in our evaluation of the software.

In this type, we first encounter the failure handing monad that we will use to
propagate errors. It works as one might expect, either succeeding with a value
or failing with an error message.
\begin{code}
findRule : List β-rule →
           (tar type elim : Const γ)  →
           Failable ( Σ[ r ∈ β-rule ] βRule-Env r)
\end{code}
\hide{
\begin{code}
findRule [] t ty e = fail ("No matching β-rule found for " ++
                           print t ++ " : " ++ print ty ++
                           " eliminated by " ++ print e)
findRule (r ∷ rs) t ty e with β-match r t ty e
... | nothing   = findRule rs t ty e
... | just env  = succeed (r , env)
\end{code}
}
To achieve reduction we will need to check the premise chain in the enclosed
elimination to access the required environments. The mechanics of
checking premise chains is not the business of $β$-reduction code and so we
instead give a type to represent a function that can do this for us and insist
that the caller provide it. We also provide a similar type appended with `
which captures the same intuition except that it is "pre-loaded" with the
context.
\begin{code}
PremsChecker =  ∀{δ} → Context δ         →
                {p q p' : Pattern δ}     →
                p -Env → q -Env          →
                Prems p q p'             →
                Failable (p' -Env)
\end{code}
Reduction with regards to a list of rules can now be defined in three stages;
we first attempt to find a matching rule, then if this succeeds we check
the premise chain and finally if both the previous stages succeed then
we make our call to $β$-reduce.
\begin{code}
reduce : List β-rule   →
         PremsChecker' γ →
         (tar type elim : Const γ)  →
         Failable (Compu γ)
reduce {γ} rules checkprems ta ty el
  = do
      (rule , t , ty , e) ← findRule rules ta ty el
      p'env ← checkprems ty e (⊗premises γ (eprems rule)) 
      succeed (β-reduce rule (t , ty , e) p'env)
    where open ElimRule
\end{code}
β-reduction failure depends solely on the existence of the rule, and the
successful checking of the premise chain. The call to β-reduce is not in
itself a failable operation.

\section{Normalisation by evaluation}
\label{section-normalisation}

We previously gave a type describing a premise-chain-checker, now
we give similar types for things that will reduce for us, and things that might
infer types. What is noticeably absent from these types is the existence of any kind
of rules. Our normalisation procedure should be rule-agnostic and so we achieve this
by taking great care in where we choose to mention them, and where we choose \emph{not}
to. We must, however, bear the rules in mind when we normalise and so a conscious
decision is made here for normalisation to be a non-failable operation. In a world of
user-supplied typing rules, we decide that flexibility is important and so when we
encounter problems we take a "do as much as you can" approach to normalisation. 
\begin{code}
Reducer  =   ∀ {γ}                      →
             PremsChecker' γ            →
             (tar type elim : Const γ)  →
             Failable (Compu γ)
Inferer  =   ∀ {γ}                      →
             Context γ                  →
             (term : Term compu γ)      →
             Failable (Term const γ)
\end{code}
To implement normalisation by evaluation, we must first define an evaluation
function to reduce any eliminations. Most cases proceed as one might expect,
traversing the structure of the term to find eliminations that we might hope to
reduce. We reduce the target and eliminator in some elimination even if we fail
to infer the type of the target (and so fail to reduce the elimination). This is
to keep separate the concerns of type-checking and normalisation and it is our
opinion that this evaluation should not fail because of a type-error. Instead, the
process continues with some $unknown$ type placeholder, meaning that it will not
match any rules that might produce erroneous results. The responsibility of type-checking
the term falls to the caller.

\hide{
\begin{code}
open import EtaRule
open η-Rule
{-# TERMINATING #-}
\end{code}
}
\begin{code}
_-_∥_∥ :  Reducer × Inferer × PremsChecker →
         Context γ →
         Term d γ →
         Const γ
(rd , inf , pc) - Γ ∥ T ∥ = ⟦ T ⟧ Γ
  where
    ⟦_⟧ : Term d γ → Context γ → Const γ
    -- ...
    ⟦_⟧ {compu} {γ} (elim t e) Γ with inf Γ t
    ... | fail    n = thunk (elim (↞↞ (⟦ t ⟧ Γ) (` "unknown")) (⟦ e ⟧ Γ))
    ... | succeed ty with rd (pc Γ) (⟦ t ⟧ Γ) ty (⟦ e ⟧ Γ)
    ... | succeed x = ⟦ x ⟧ Γ
    ... | fail x    = thunk (elim (↞↞ (⟦ t ⟧ Γ) ty) (⟦ e ⟧ Γ))
    -- ...

\end{code}
\hide{
\begin{code}
    ⟦_⟧ {const} (` x) Γ       = ` x
    ⟦_⟧ {const} (s ∙ t) Γ     = ⟦ s ⟧ Γ ∙ ⟦ t ⟧ Γ
    ⟦_⟧ {const} (bind t) Γ    = bind (⟦ t ⟧ (Γ Context., ` "unknown") )
    ⟦_⟧ {const} (thunk x) Γ   = ⟦ x ⟧ Γ
    ⟦_⟧ {compu} (var x) Γ     = thunk (var x)
    ⟦_⟧ {compu} (t ∷ T) Γ   = ⟦ t ⟧ Γ
{-# TERMINATING #-}    
\end{code}
}

The final step in normalisation by evaluation is trying to build the correct head
form for the associated types of the term and its subterms. We do this using our
η-Rule mechanics from \ref{section-etarules}, our svar-builder from \ref{section-patterns}
and our method of computing the type of a place in a pattern given some $∋$-rule
from \ref{section-rules}.

Here we match some η-rule giving us the pattern for the head form, and also the
eliminations that will occur at each place in that pattern. We then navigate down
through the structure of the head pattern in our helper function so that we
get to each place in the pattern, and when we do, we have built the svar that
identifies it. This allows us to use the ∋ rule to get the type of that particular
place which in turn facilitates the recursive call to qt to generate the head form
at the nested place.

To satisfy the well-scopedness of the subterms, we must maintain a proof
that we are constructing a well-scoped svar-builder. When we traverse under a binder
in a head form pattern, we are forced to add such a binder to our svar-builder to
maintain its well-scopedness. Our proof achieves this by maintaining the invariant
that the scope of the subterm currently identified by the svar-builder is always the
original scope plus however many binders we have added when constructing it.

\begin{code}
qt : List η-Rule → (ty tm : Const γ) → Const γ
qt {γ = γ} rs ty v with EtaRule.findRule rs ty
... | fail x           = v
... | succeed (r , i)  = let elms = eliminations r ty v in
                            helper (γ ⊗ headForm r) (i ∙ elms) X refl elms
  where
    ∋rl = checkRule r
    helper : ∀ {γ'}(q : Pattern γ')                       →
             ((γ ⊗ input ∋rl) ∙ (γ ⊗ subject ∋rl))-Env    →         
             (v : svar-builder (γ ⊗ subject ∋rl) q)       →
             γ' ≡ bind-count-bl v + γ                     →
             q -Env                                       →
             Const (bind-count-bl v + γ)
    helper (` x)    is v prf `
      = ` x
    helper (s ∙ t)  is v prf (es ∙ et)
      = helper s is (⇚ v) prf es ∙ helper t is (⇛ v) prf et
    helper (bind q) is v prf (bind et) 
      = bind (helper q is (↳ v) (cong suc prf) et)
    helper (place θ) (i ∙ s) v prf (thing el)
      = qt rs
           (typeOf (checkRule r) (build v) i s)
           (subst Const prf (el ⟨term θ))
\end{code}
With the heavy lifting completed normalisation is then just a process of first
evaluating the term before building suitable head forms.
\begin{code}
normalize :  List η-Rule → List β-rule  →
             Inferer × PremsChecker     →
             Context γ                  →
             (type : Const γ)           →
             (term : Term d γ)          →
             Const γ
normalize ηs βs i&c Γ ty = (qt ηs ty) ∘ ((reduce βs , i&c) - Γ ∥_∥)
\end{code}
