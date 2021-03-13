\section{}

\hide{
\begin{code}
module SpecParser where
\end{code}
}

\hide{
\begin{code}
open import CoreLanguage
open import Pattern hiding (map; _≟_)
open import Thinning using (ι)
open import Category.Monad using (RawMonad)
open import Data.List hiding (lookup; map; fromMaybe; foldr; all)
open import Data.Product using (_×_; Σ-syntax; _,_; Σ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Char hiding (_≟_; show)
open import Data.String using (String)
open import Data.Maybe using () renaming (maybe′ to maybe)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Nat using (suc; ∣_-_∣; _<″_; _≤″?_)
open import Data.Bool using (Bool; _∧_; _∨_; not; if_then_else_)
open import Function using (_∘′_)
open import Thinning using (_⊑_)
import Data.Tree.AVL.Map as MapMod
open MapMod <-strictTotalOrder-≈
open import Parser as P
open P.Parser
open P.Parsers
\end{code}
}

\hide{
\begin{code}
private
  variable
    δ : Scope
    γ : Scope
    γ' : Scope
    p : Pattern δ
\end{code}
}

We define mappings for variable names to svars, and create a type for pattern
parsers which aim to parse some pattern along with mappings from names to
svars in the pattern. This map is used to retrieve the svars when parsing
components such as expressions which depend on this.

\begin{code}
SVar : Pattern γ → Set
SVar p = Σ[ δ ∈ Scope ] svar p δ 

SVarMap : Pattern γ → Set
SVarMap p = Map (SVar p)

_-svmap_ : SVarMap p → (ξ : svar p γ) → SVarMap (p - ξ)
map -svmap ξ  = foldr (λ k (δ , v) t → maybe (λ v → insert k (δ , v) t) t (v -svar ξ)) empty map

PatternParser : Scope → Set
PatternParser γ = Parser (Σ[ p ∈ Pattern γ ] SVarMap p)
\end{code}

\begin{code}
module PatternParser where
  open parsermonad
  
  forbidden-atom-chars : List Char
  forbidden-atom-chars = '(' ∷ ')' ∷ '{' ∷ '}' ∷ '[' ∷ ']' ∷ '.' ∷ ':' ∷ ',' ∷ []
  
  atomchar : Char → Bool
  atomchar c = isLower c ∨ ( not (isAlpha c) ∧ not (isSpace c) ∧ not (any (c ==_) forbidden-atom-chars))
  
  idchar : Char → Bool
  idchar c = isAlpha c ∧ (not (isLower c))

      
  identifier : Parser String
  identifier = nonempty (stringof idchar)  
  
  binding : Parser String
  binding = do
              name ← identifier
              literal '.'
              return name

\end{code}
  
\begin{code}
  pat : PatternParser γ
  private
    atom : PatternParser γ
    atom = (_, empty) <$> (` <$> nonempty (stringof atomchar))     
    
    plc : PatternParser γ
    plc {γ} = do
                name ← identifier
                ifp literal '.' then fail
                                else return ((place ι) , singleton name (γ , ⋆))

    {-# TERMINATING #-}
    binder : PatternParser γ
    binder {γ} = do
                   name ← safe binding
                   whitespace
                   (subterm , vmap) ← pat {suc γ}
                   return ((bind subterm) , map (λ {(δ , st) → (δ , bind st)  }) vmap)
    
  pat {γ} = do
              (fst , vmap) ← anyof(atom {γ} ∷ plc ∷ binder ∷ bracketed pat ∷ [])              
              inj₁ (snd , vmap') ← optional (do
                                               whitespace
                                               pat {γ})
                where inj₂ _ → return (fst , vmap)
              return ((fst ∙ snd) , union (map (λ { (δ , st) → (δ , (st ∙))}) vmap)
                                          (map (λ { (δ , st) → (δ , (∙ st))}) vmap'))

  closed-pattern = pat {0}
open PatternParser
\end{code}

Now we must parse expressions. The parsing of an expression must be done in
terms of a pattern, but also a mapping from variable names to svars, thus the
user does not have to deal with the svars externally.

\begin{code}
{-
  If we want to refer to variables by name in our expressions, then we have to
  use another map

  Also, tidy up these types ya animal
-}

module ExpressionParser where
  open import Expression hiding (map)
  open import Data.Maybe using (maybe′)
  open import Data.Nat using (zero; _≟_)
  open import Relation.Nullary using (yes; no)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Substitution using (_⇒[_]_)
  open import BwdVec using (ε; _-,_)
  open parsermonad

  VarMap : Scoped
  VarMap γ = Map (Var γ)

  private
    variable
      δ' : Scope

  ConstParser = ∀ {δ} → (p : Pattern δ) → (γ : Scope) → VarMap γ → SVarMap p → Parser (Expr p const γ)
  CompuParser = ∀ {δ} → (p : Pattern δ) → (γ : Scope) → VarMap γ → SVarMap p → Parser (Expr p compu γ)
    
  econst : ConstParser
  ecompu : CompuParser

  schvar : (p : Pattern γ) → SVarMap p → Parser (SVar p × String)
  schvar p svmap = do
                     name ← identifier
                     ifp literal '.' then fail
                                     else maybe′ (return ∘′ (_, name)) fail (lookup name svmap)

  private
    eatom : ConstParser
    eatom _ _ _ _ = ` <$> nonempty (stringof atomchar) 
    
    {-# TERMINATING #-}
    ebinder : ConstParser
    ebinder p γ vmap svmap = do
                         name ← safe binding
                         whitespace
                         subexpr ← econst p (suc γ) (insert name ze (map su vmap)) svmap
                         return (bind subexpr)
    
    ethunk : ConstParser
    ethunk p γ vmap svmap = do
                        comp ← curlybracketed (ecompu p γ vmap svmap)
                        return (thunk comp)

    open import Data.Maybe using (just)
    eσ : (δ γ : Scope) → (p : Pattern δ') → VarMap γ → SVarMap p → Parser (δ ⇒[ Expr p compu ] γ)
    eσ zero γ p vmap svmap    = return ε
    eσ (suc δ) γ p vmap svmap = do
                                  rest ← eσ δ γ p vmap svmap
                                  ws-tolerant (literal ',')
                                  this ← ecompu p γ vmap svmap
                                  return (rest -, this)
    open import Data.Nat.Show using (show)
    open import Data.String using (_++_)
    einst : ConstParser
    einst p γ vmap svmap = do
                             ((δ , ξ) , name) ← schvar p svmap
                             yes refl ← return (δ ≟ 0)
                               where no _ → do
                                              literal '/'
                                              σ ← squarebracketed (eσ δ γ p vmap svmap)
                                              return (ξ / σ)
                             return (ξ / ε)
                             
    evar : CompuParser
    evar p γ vmap svmap = do
                               literal '.'
                               name ← identifier
                               maybe′ (return ∘′ var) fail (lookup name vmap)         
    
    erad : CompuParser
    erad p γ vmap svmap = do
                            t ← econst p γ vmap svmap
                            ws-tolerant (literal ':')
                            T ← econst p γ vmap svmap
                            return (t ∷ T)
    
  econst p γ vmap svmap = do
             fst ← anyof (eatom   p γ vmap svmap  ∷
                          ebinder p γ vmap svmap  ∷
                          ethunk  p γ vmap svmap  ∷
                          einst   p γ vmap svmap  ∷
                          bracketed (econst p γ vmap svmap) ∷ [])
             inj₁ snd ← optional (do
                                  whitespace
                                  econst p γ vmap svmap)
               where inj₂ _ → return fst
             return (fst ∙ snd)

  ecompu p γ vmap svmap = do
             fst ← anyof (evar p γ vmap svmap ∷
                          erad p γ vmap svmap ∷
                          bracketed (ecompu p γ vmap svmap) ∷ [])
             inj₁ eliminator ← optional (do
                                           whitespace
                                           econst p γ vmap svmap)
                  where inj₂ _ → return fst                  
             return (elim fst eliminator)
open ExpressionParser
\end{code}

With our ability to parse patterns and expressions, we can now parse
premise and premise chains. In general, to parse a premise we must know
everything that is trusted and what we still have to trust.


\begin{code}

module PremiseParser where

  open import Rules using (Prem; _∋'_[_]; _≡'_; univ; _⊢'_; type)
  open import Data.Nat using () renaming(_≟_ to _≟n_)
  open import Pattern using (_-svar_)
  open import Data.Maybe using () renaming (maybe′ to maybe)
  open import Relation.Nullary using (yes; no)
  open import Relation.Binary.PropositionalEquality using (refl)
  import Data.Tree.AVL using (foldr)  
  open parsermonad

  PremiseParser : Set
  PremiseParser = ∀ {δ}{γ} →
                  (p q : Pattern δ) →
                  (SVarMap p) → (SVarMap q) → (VarMap γ) → 
                  Parser (Σ[ (p' , q') ∈ (Pattern γ × Pattern δ) ]
                          SVarMap p' × SVarMap q' × Prem p q γ p' q')

  prem : PremiseParser

  typeprem : PremiseParser
  typeprem {γ = γ} p q pmap qmap vm
    = do
        string "type"
        whitespace
        ((δ' , ξ) , name) ← schvar q qmap
        yes refl ← return (δ' ≟n γ)
          where no _ → fail
        return (((place ι) , (q - ξ)) , (singleton name (δ' , ⋆) , qmap -svmap ξ , type ξ ι))

  ∋prem : PremiseParser
  ∋prem {γ = γ} p q pmap qmap vm
    = do
        T ← bracketed (econst p γ vm pmap)
        ws-tolerant (string "<-")
        ((δ' , ξ) , name) ← schvar q qmap
        yes refl ← return (δ' ≟n γ)
          where no _ → fail
        return ((place ι , (q - ξ)) , (singleton name (δ' , ⋆) , qmap -svmap ξ , (T ∋' ξ [ ι ])))

  ≡prem : PremiseParser
  ≡prem {γ = γ} p q pmap qmap vm
    = do
        S ← bracketed (econst p γ empty pmap)
        ws-tolerant (literal '=')
        T ← econst p γ empty pmap
        return (((` "⊤") , q) , (empty , qmap , (S ≡' T)))

  univprem : PremiseParser
  univprem {γ = γ} p q pmap qmap vm
    = do
        string "univ"
        whitespace
        U ← econst p γ empty pmap
        return (((` "⊤") , q) , (empty , qmap , univ U))

  {-# TERMINATING #-}
  ⊢prem : PremiseParser
  ⊢prem {γ = γ} p q pmap qmap vm
    = do
        name ← identifier
        ws-tolerant (literal ':')
        S ← (safe ∘′ bracketed) (econst p γ empty pmap)
        ws-tolerant (string "|-")
        ((p' , q'), (p'm , q'm , P)) ← prem {γ = suc γ} p q pmap qmap (insert name ze (map su vm))
        return ((bind p' , q') , (map (λ {(δ , v) → (δ , bind v)} ) p'm , q'm , (S ⊢' P)))
  open import Expression using (`)
  prem p q pmap qmap vm
    = anyof (Data.List.map (λ pp → pp p q pmap qmap vm)
            (typeprem ∷ ∋prem ∷ ≡prem ∷ univprem ∷ ⊢prem ∷ []))
open PremiseParser            
\end{code}

-- Premise chains:

\begin{code}

module PremisechainParser where

  open import Rules using (Prems; ε; _⇉_; _Placeless; _-places; _placeless)
  open import Pattern using (_≟_)
  open import Relation.Nullary using (yes; no)
  open import Relation.Binary.PropositionalEquality using (refl; subst)
  open parsermonad

  PremisechainParser = 
                     (p q : Pattern 0) →
                     (SVarMap p) → (SVarMap q) →
                     Parser (Σ[ p' ∈ Pattern 0 ]
                             SVarMap p' × Prems p q p')
                             
  chain : PremisechainParser
  
  private
    εchain : PremisechainParser           
    εchain p q pmap qmap
      = do
          yes eq ← return ((q -places) ≟ q)
            where no p → fail
          return (p , (pmap , ε (subst (λ x → x Placeless) eq (q placeless))))
    
    {-# TERMINATING #-}
    nonε-chain : PremisechainParser
    nonε-chain p q pmap qmap
      = do
          ((p' , q') , (p'm , q'm , prm)) ← prem {γ = 0} p q pmap qmap empty
          ws+nl
          (p' , p'm , rest) ← chain (p ∙ p') q'  (union
                                                   (map (λ {(s , v) → (s , v ∙)}) pmap)
                                                   (map (λ {(s , v) → (s , ∙ v)}) p'm))
                                             q'm
          return (p' , p'm , (prm ⇉ rest))
    
  chain p q pmap qmap = either (nonε-chain p q pmap qmap)
                            or (εchain p q pmap qmap)

  pchain : PremisechainParser
  pchain p q pmap qmap = either
                           (do
                              string "if:"
                              ws+nl
                              chain p q pmap qmap)
                         or
                           (εchain p q pmap qmap)                      
open PremisechainParser  
\end{code}

We can now parse the whole specification file, the result of which is an entire set of rules.

\begin{code}

module SpecfileParser where

  open import TypeChecker using (RuleSet; rs)
  open import Rules using (UnivRule; TypeRule; ∋rule; ElimRule; ε; _placeless)
  open import Expression using (Con; `) renaming (map to emap)
  open import Semantics using (β-rule)
  open import Pattern using (←_)
  open import Data.Product using (proj₁)
  open parsermonad

  tester : ElimRule
  ElimRule.targetPat tester = ` ""
  ElimRule.eliminator tester = ` ""
  ElimRule.premises tester = (` "") , (Rules.ε ((` "") Rules.placeless))
  ElimRule.output tester = ` ""

  β : (t : Pattern 0) → (er : ElimRule) → SVarMap (t ∙ ElimRule.targetPat er ∙ ElimRule.eliminator er) → Parser β-rule
  β t er svmap = do
            string "reduces-to:"
            whitespace 
            redTerm ← econst (t ∙ targetPat er ∙ eliminator er) 0 empty svmap
            return (record
                    { target = t
                    ; erule = er
                    ; redTerm = redTerm
                    })
           where open ElimRule

  thingy' : Set
  thingy' = Σ[ e ∈ ElimRule ] (SVarMap (ElimRule.targetPat e)× SVarMap (ElimRule.eliminator e))

  thingy : Set
  thingy = List thingy'

  [β] : (t : Pattern 0) → SVarMap t → thingy → Parser (List β-rule)
  [β] _ _ [] = return []
  [β] t svt ((er , svty , sve) ∷ xs)
    = do
        r ← β t er ((union
                      (map (λ {(δ , v) → (δ , (v ∙))}) svt)
                      (union
                        (map (λ (δ , v) → (δ , (∙ (v ∙)))) svty)
                        (map (λ {(δ , v) → (δ , (∙ (∙ v)))}) sve))))
        ws+nl
        rls ← [β] t svt xs
        return (r ∷ rls)

  ∋ : (ty tm : Pattern 0) → SVarMap ty → SVarMap tm → Parser ∋rule
  ∋ ty tm tyvars tmvars = do
                 (p' , p'm , pc) ← pchain ty tm tyvars tmvars
                 return (record { subject = tm ; input = ty ; premises = (p' , pc) })


  value : (tty : Pattern 0) → SVarMap tty → thingy → Parser (∋rule × List (β-rule))
  value tty ttymap els = do
                    string "value:"                    
                    (c , m) ← ws-tolerant closed-pattern
                    ws+nl
                    ∋r ← ∋ tty c ttymap m
                    ws+nl
                    βrls ← [β] c m els                                        
                    return (∋r , βrls)

  values : (tty : Pattern 0) → SVarMap tty → thingy → Parser (List ∋rule × List (β-rule))
  values tty ttymap els = do
                            rst ← wsnl-tolerant (value tty ttymap els)
                                      *[ (λ {(∋r , newβrs) (∋rs , βrs) → (∋r ∷ ∋rs) , newβrs ++ βrs})
                                      , ([] , []) ]
                            return rst

  eliminator : (tty : Pattern 0) → SVarMap tty → Parser thingy'
  eliminator tty ttymap = do
                            string "eliminated-by:"
                            (e , m) ← ws-tolerant closed-pattern
                            ws+nl
                            (p' , p'm , pc) ← pchain tty e ttymap m
                            ws+nl
                            string "resulting-in-type:"
                            et ← ws-tolerant (econst p' 0 empty p'm)
                            return ((record
                                       { targetPat = tty ; eliminator = e ; premises = p' , pc ; output = et }) , (ttymap , m))


  eliminators : (tty : Pattern 0) → SVarMap tty → Parser (thingy)
  eliminators tty ttymap = do
                             rst ← wsnl-tolerant (eliminator tty ttymap) *[ _∷_ , [] ]
                             return rst

  open import Data.Unit using (⊤; tt)
  eta : Parser ⊤
  eta = do
          string "expanded-by:"
          ws-tolerant closed-pattern
          return tt

  type : Parser RuleSet
  type = do
           string "type:"
           (ty , ty-map) ← ws-tolerant closed-pattern
           ws+nl
           (p' , p'm , pc) ← pchain (` "⊤") ty empty ty-map
           tr ← return (record { subject = ty ; premises = (p' , pc) } ∷ [])
           ws+nl
           elim-rules ← eliminators ty ty-map
           ws+nl
           (∋rs , βrs) ← values ty ty-map elim-rules
           ws+nl
           optional eta
           return (rs tr [] ∋rs (Data.List.map proj₁ elim-rules) βrs [])

  setType : TypeRule
  TypeRule.subject setType = ` "set"
  TypeRule.premises setType = ` "⊤" , ε (` "set" placeless)

  setUniv : UnivRule
  UnivRule.input setUniv = ` "set"
  UnivRule.premises setUniv = ` "set" , (ε (` "⊤" placeless))

  parse-spec : Parser RuleSet
  parse-spec = do
                 (rs ty u ∋ e β η) ← (wsnl-tolerant type) ⁺[ (λ {(rs a  b  c  d  e  f)
                                     (rs a' b' c' d' e' f') →
                                     rs (a ++ a') (b ++ b') (c ++ c') (d ++ d') (e ++ e') (f ++ f')}) , rs [] [] [] [] [] [] ]
                 return (rs (setType ∷ ty) (setUniv ∷ u) ∋ e β η)
open SpecfileParser
\end{code}

