module Test.SpecReadingTest where

  open import IO.Primitive
  open import CoreLanguage
  import SpecParser as SP
  open SP.SpecfileParser using (parse-spec)
  import LanguageParser
  open import TypeChecker using (RuleSet; rs; infer)
  open import Pattern using (Pattern; print-pat)
  open import Data.List using (List; _∷_; []; foldr; length) renaming (map to lmap)
  open import BwdVec using (ε)
  open import Data.Unit using (⊤; tt)
  open import Data.Maybe using (just; nothing)
  open import Data.Product using (_,_)
  open import Failable using (succeed; fail)
  open import Data.String using (String; _++_; words)
  open import Data.String.Properties using (<-strictTotalOrder-≈)
  open import Codata.Musical.Costring
  open import Data.List using (length)
  open import Data.Nat.Show using (show)
  import Data.Tree.AVL.Map as MapMod
  open MapMod <-strictTotalOrder-≈ using (empty)
  open import Function using (_∘′_)
  open import Rules using (TypeRule)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  -- UNCOMMENT THIS TO GET A COMPILABLE BINARY TO TEST IF REQUIRED

  open LanguageParser.LParsers
  main : IO ⊤
  main = do
           desc ← readFiniteFile "/home/grant/Uni/CS408-Project/TypeCheckerGenerator/Test/Specs/STLCTST.desc"
           src  ← readFiniteFile "/home/grant/Uni/CS408-Project/TypeCheckerGenerator/Test/Specs/STLCSource.desc"
           just (rules@(rs tr ur ∋r er βr ηr) , rest) ← return (parse-spec desc)
             where nothing → putStrLn (toCostring "Failed to parse spec file")
           _ ← putStrLn (toCostring ("Parsed:\n" ++ show (length tr) ++ " types\n" ++ show (length ∋r) ++ " introduction forms\n" ++ show (length er) ++ " elimination typing rules\n" ++ show (length βr) ++ " β-rules\n"))
           _ ← putStrLn (toCostring "Parsing source file ...")
           just (term , rest) ← return (computation (tr , ∋r , er) empty src)
             where nothing → putStrLn (toCostring "Failed to parse source code file.")
           _ ← putStrLn (toCostring ("term parsed: " ++ print term))
           _ ← putStrLn (toCostring ("ignored: " ++ rest ++ "\n"))
           succeed type ← return (infer rules ε term)
             where fail msg → putStrLn (toCostring msg)
           _ ← putStrLn (toCostring ("te#rm: " ++ (print term) ++ "\ntype: " ++ print type)) 
           return tt
{-

  open import Rules using (∋rule; TypeRule; ElimRule; ε; _⇉_; type; _∋'_[_]; _⊢'_; _placeless)
  open import Pattern using (Pattern; `; _∙_; bind; place; ∙_; _∙; ⋆)
  open import Expression using (`; _/_)
  open import Data.List using (_∷_; [])
  open import Thinning using (ι)
  open ∋rule
  open TypeRule
  open ElimRule
  open import LanguageParser


  t : TypeRule
  subject t = place ι ∙ ` "->" ∙ place ι
  premises t = (((` "⊤" ∙ place ι) ∙ place ι)) , (type (⋆ ∙) ι ⇉ type (∙ ∙ ⋆) ι ⇉ ε ((` "⊤" ∙ ` "->" ∙ ` "⊤") placeless))

  t' : TypeRule
  subject t' = ` "alpha"
  premises t' = (` "⊤") , (ε (` "alpha" placeless))

  r' : ∋rule
  subject r' = ` "a"
  input r' = ` "alpha"
  premises r' = (` "alpha") , (ε (` "a" placeless))

  beta : TypeRule
  subject beta = ` "beta"
  premises beta = (` "⊤") , (ε (` "beta" placeless))

  b : ∋rule
  subject b = ` "b"
  input b = ` "beta"
  premises b = (` "beta") , (ε (` "b" placeless))

  r : ∋rule
  subject r = ` "lam" ∙ bind (` "->" ∙ (place ι))
  input r = subject t
  premises r = input r ∙ bind (place ι) , ((` "" ⊢' type (∙ bind (∙ ⋆)) ι) ⇉ ε ((` "lam" ∙ bind (` "->" ∙ (place ι))) placeless))

  pairType : TypeRule
  subject pairType = ` "both" ∙ (place ι) ∙ (place ι)
  premises pairType = (` "⊤" ∙ place ι) ∙ place ι , (type (∙ (⋆ ∙)) ι ⇉ type (∙ ∙ ⋆) ι ⇉ ε ((` "both" ∙ ` "⊤" ∙ ` "⊤") placeless))

  pair∋ : ∋rule
  subject pair∋ = place ι ∙ ` "and" ∙ place ι
  input pair∋ = subject pairType
  premises pair∋ = (input pair∋ ∙ place ι) ∙ place ι ,
                          ((((∙ (⋆ ∙)) / ε) ∋' ⋆ ∙ [ ι ]) ⇉
                          ((((∙ ∙ ⋆) ∙) / ε) ∋' ∙ ∙ ⋆ [ ι ]) ⇉
                          ε ((` "⊤" ∙ ` "and" ∙ ` "⊤") placeless))

  er1 : ElimRule
  targetPat er1 = subject pairType
  eliminator er1 = ` "fst"
  premises er1 = (subject pairType) , (ε (` "fst" placeless))
  output er1 = (∙ (⋆ ∙)) / ε

  er2 : ElimRule
  targetPat er2 = subject pairType
  eliminator er2 = ` "snd"
  premises er2 = (subject pairType) , (ε (` "snd" placeless))
  output er2 = (∙ (∙ ⋆)) / ε

  rules : Rules
  rules = (t ∷ t' ∷ beta ∷ pairType ∷ [] , r ∷ r' ∷ b ∷ pair∋ ∷ [] , er1 ∷ er2 ∷ [])

  import LanguageParser
  open LanguageParser.LParsers rules



  ans1 = construction {0} empty "lam x -> x"

  _ : ans1 ≡ just (` "lam" ∙ bind (` "->" ∙ thunk (var ze)) , "")
  _ = refl

  ans2 = construction {0} empty "(alpha -> alpha) -> alpha"
  _ : ans2 ≡ just ((` "alpha" ∙ ` "->" ∙ ` "alpha") ∙ ` "->" ∙ ` "alpha" , "")
  _ = refl

  ans3 = computation {0} empty "(lam x -> x : alpha -> alpha) "

  _ : ans3 ≡ just
      (((` "lam" ∙ bind (` "->" ∙ thunk (var ze))) ∷
        (` "alpha" ∙ ` "->" ∙ ` "alpha"))
       , " ")
  _ = refl
  
  ans4 = computation {0} empty "(lam x -> a : ((alpha -> alpha) -> alpha)) "

  _ : ans4 ≡ just
      (((` "lam" ∙ bind (` "->" ∙ ` "a")) ∷
        ((` "alpha" ∙ ` "->" ∙ ` "alpha") ∙ ` "->" ∙ ` "alpha"))
       , " ")
  _ = refl

  ans5 = computation {0} empty "((lam x -> a) : ((alpha -> alpha) -> alpha)) "

  _ : ans5 ≡ just
      (((` "lam" ∙ bind (` "->" ∙ ` "a")) ∷
        ((` "alpha" ∙ ` "->" ∙ ` "alpha") ∙ ` "->" ∙ ` "alpha"))
       , " ")
  _ = refl
  
  ans6 = computation {0} empty "(((lam x -> a) : (alpha -> alpha) -> alpha)(lam x -> x))"

  _ : ans6 ≡ just
      (elim
        ((` "lam" ∙ bind (` "->" ∙ ` "a")) ∷
            ((` "alpha" ∙ ` "->" ∙ ` "alpha") ∙ ` "->" ∙ ` "alpha"))
        (` "lam" ∙ bind (` "->" ∙ thunk (var ze)))
       , "")
  _ = refl

  ans7 = computation {0} empty "(\n((lam x -> a) : (alpha -> alpha) -> alpha)\n(lam x -> x)\n)"

  _ : ans7 ≡ just
      (elim
       ((` "lam" ∙ bind (` "->" ∙ ` "a")) ∷
        ((` "alpha" ∙ ` "->" ∙ ` "alpha") ∙ ` "->" ∙ ` "alpha"))
       (` "lam" ∙ bind (` "->" ∙ thunk (var ze)))
       , "")
  _ = refl

  ans8 = computation {0} empty "(\n (lam x -> a : alpha -> alpha)\n (\n ((lam x -> a) : (alpha -> alpha) -> alpha)\n lam x -> x\n )\n )"

  _ : ans8 ≡ just
      (elim
       ((` "lam" ∙ bind (` "->" ∙ ` "a")) ∷
        (` "alpha" ∙ ` "->" ∙ ` "alpha"))
       (thunk
        (elim
         ((` "lam" ∙ bind (` "->" ∙ ` "a")) ∷
          ((` "alpha" ∙ ` "->" ∙ ` "alpha") ∙ ` "->" ∙ ` "alpha"))
         (` "lam" ∙ bind (` "->" ∙ thunk (var ze)))))
       , "")
  _ = refl

  ans9 = computation {0} empty "((lam f -> (f a)) : ((alpha -> alpha) -> alpha))"

  _ : ans9 ≡ just
      (((` "lam" ∙ bind (` "->" ∙ thunk (elim (var ze) (` "a")))) ∷
        ((` "alpha" ∙ ` "->" ∙ ` "alpha") ∙ ` "->" ∙ ` "alpha"))
       , "")
  _ = refl


  ans10 = construction {0} empty "((both alpha beta) -> both alpha beta)"

  _ : ans10 ≡ just
               ((` "both" ∙ ` "alpha" ∙ ` "beta") ∙
                ` "->" ∙ ` "both" ∙ ` "alpha" ∙ ` "beta"
                , "")
  _ = refl

  ans11 = construction {0} empty "((both alpha beta) -> (both alpha beta))"

  _ : ans11 ≡ just
               ((` "both" ∙ ` "alpha" ∙ ` "beta") ∙
                ` "->" ∙ ` "both" ∙ ` "alpha" ∙ ` "beta"
                , "")
  _ = refl


  ans12 = construction {0} empty "lam x -> (x snd) and (x fst)"

  _ : ans12 ≡ just
                (` "lam" ∙
                 bind
                 (` "->" ∙
                  thunk (elim (var ze) (` "snd")) ∙
                  ` "and" ∙ thunk (elim (var ze) (` "fst")))
                 , "")
  _ = refl
  
  ans13 = computation {0} empty "(lam x -> (x snd) and (x fst) : ((both beta alpha) -> (both alpha beta)))"

  _ : ans13 ≡ just
                (((` "lam" ∙
                   bind
                   (` "->" ∙
                    thunk (elim (var ze) (` "snd")) ∙
                    ` "and" ∙ thunk (elim (var ze) (` "fst"))))
                  ∷
                  ((` "both" ∙ ` "beta" ∙ ` "alpha") ∙
                   ` "->" ∙ ` "both" ∙ ` "alpha" ∙ ` "beta"))
                  , "")
  _ = refl


-}
