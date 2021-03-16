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

Given the way that we represent typing rules, our type for $β$-rules
should not look unfamiliar. We match an $β$-rule by matching patterns
for the target, and then matching some elimination rule using the
target type and the eliminator. We then provide an expression that
constructs the reduced term. Since we can work out the type of the
reduced term using the included elimination rule, we have all we need
to build a computation: either the reduced term is some thunk and
we already have a computation under it, or it is not a thunk but we
can use the type that we know to annotate it. This is the essence of
the $↞↞$ operater that we introduced in section \ref{section-corelanguage}.

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
We then define a function that will attempt a reduction with regards
to a list of β-rules by trying to match and apply a rule. First, for
convenience and readability, we create a type to represent something
that checks the premises, the result of which is either failure, or
success where success returns an environment for everything we have
learned to trust. The $'$ version of this type is a similar story
except it is a type constructor that accepts some scope and returns
the type of something able to check premises that is pre-loaded with
a context.
\begin{code}
PremsChecker =  (δ : Scope) → Context δ  →
                {p q p' : Pattern δ}     →
                p -Env → q -Env          →
                Prems p q p'             →
                Failable (p' -Env)
\end{code}
\hide{
\begin{code}
open import Failable using (_>>=_)
\end{code}
}
We not give the type of the function that is responsible for trying to
return a matching βRule (and an environment for the various patterns so
that we might use it) after which reduction involves finding some rule (where
we here get some of the environment information we need) then checking the
opened premise chain (where we get the rest of the environment information
we need) before finally making a call to reduce with this information.
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
One aspect worth noting here, is that β-reduction failure depends solely on the
existance of the rule, and the successful checking of the premise chain. The call
to β-reduce is not in itself a failable operation.

\section{Normalisation by evaluation}

We previously gave a type describing what a premise checker might look like, now
we give similar types for things that will reduce for us, and things that might
infer types. What is noticeably absent from these types is the existance of any kind
of rules. Our normalisation procedure should be rule agnostic and so we achieve this
by not talking about rules at all. We must, however, bear the rules in mind when
we normalise. A concious decision was made here for this to be a non-failable
operation. In a world of user-supplied typing rules we decide that flexibility
is important and so when we encounter problems we take a "do as much as you can"
approach to normalisation. 
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
In order to implement normalisation by evaluation, we must first define an evaluation
function to reduce any eliminations. Most cases proceed as one might expect,
traversing the structure of the term to find eliminations that we might hope to
reduce. We make the decision to continue to reduce the target and eliminator in
some elimination even if we fail to infer the type of the target (and so fail to
reduce the elimination). This is to keep seperate the concerns of type-checking
and normalisation and it is our opinion that this evaluation should not fail
because of a type-error. Instead the process continues with some $unknown$ type
placeholder, meaning that it will not match any rules that might produce erroneous
results. The responsibility of type-checking the term falls to the caller.

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
    ... | succeed ty with rd (pc γ Γ) (⟦ t ⟧ Γ) ty (⟦ e ⟧ Γ)
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
identifies it. This allows us to use to ∋ rule to get the type of that particular
place which in turn facilitates the recursive call to qt to generate the head form
at the nested place.

This definition was interesting as in order to satify the well-scopedness of
the subterms, we must maintain a proof that we are constructing a well scoped
svar-builder. When we traverse under a binder in a head form pattern, we are forced
to add such a binder to our svar-builder to maintain its well-scopedness. Our proof
achieves this by maintaining the invariant that the scope of 'what is left' is
always the original scope plus however many binders we have added when constructing
the svar. As we learned the hard way, it is much easier to supply a trivial proof
of this early on and maintain it than it is to build such a proof at the "leaf".

\begin{code}
qt : List η-Rule → (ty tm : Const γ) → Const γ
qt {γ = γ} rs ty v with EtaRule.findRule rs ty
... | fail x           = v
... | succeed (r , i)  = let elms = eliminations r ty v in
                            helper (γ ⊗ headForm r) (i ∙ elms) X refl elms
  where
    ∋rl = checkRule r
    helper : ∀ {γ'}(q : Pattern γ')                       →
             ((γ ⊗ input ∋rl) ∙ (γ ⊗ subject ∋rl))-Env  →         
             (v : svar-builder (γ ⊗ subject ∋rl) q)     →
             γ' ≡ bind-count-bl v + γ                     →
             q -Env                                       →
             Const (bind-count-bl v + γ)
    helper (` x)    is v prf `
      = ` x
    helper (s ∙ t)  is v prf (es ∙ et)
      = helper s is (⇚ v) prf es ∙ helper t is (⇛ v) prf et
    helper (bind q) is v prf (bind et) 
      = bind (helper q is (↳ v) (cong suc prf) et)
    helper {γ' = γ'} (place θ) (i ∙ s) v prf (thing el)
      = qt rs
           (typeOf (checkRule r) (build v) i s)
           (subst Const prf (el ⟨term θ))
\end{code}
With the heavy lifting completed normalisation is then just a process of first
evaluating the term before building a suitable head forms.
\begin{code}
normalize :  List η-Rule → List β-rule  →
             Inferer × PremsChecker     →
             Context γ                  →
             (type : Const γ)           →
             (term : Term d γ)          →
             Const γ
normalize ηs βs i&c Γ ty = (qt ηs ty) ∘ ((reduce βs , i&c) - Γ ∥_∥)
\end{code}
