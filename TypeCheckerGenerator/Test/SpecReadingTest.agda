module Test.SpecReadingTest where

  open import IO.Primitive
  open import CoreLanguage
  import SpecParser as SP
  open SP.SpecfileParser using (parse-spec)
  open import LanguageParser using (computation; construction)
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

  --term : Compu 0
  --term = elim ((` "\\" ∙ bind (` "->" ∙ thunk (var ze))) ∷ (` "alpha" ∙ ` "->" ∙ ` "alpha")) (` "a")
{-
  print-list : ∀ {γ} → List (Pattern γ) → String
  print-list = foldr (_++_ ∘′ ((" || " ++_) ∘′ print-pat)) ""

  main : IO ⊤
  main = do
           desc ← readFiniteFile "/home/grant/Uni/CS408-Project/TypeCheckerGenerator/Test/Specs/STLC.desc"
           src  ← readFiniteFile "/home/grant/Uni/CS408-Project/TypeCheckerGenerator/Test/Specs/STLCSource.desc"
           just (rules@(rs tr ur ∋r er βr ηr) , rest) ← return (parse-spec desc)
             where nothing → putStrLn (toCostring "Failed to parse spec file")
           _ ← putStrLn (toCostring ("Parsed:\n" ++ show (length tr) ++ " types\n" ++ show (length ∋r) ++ " introduction forms\n" ++ show (length er) ++ " elimination typing rules\n" ++ show (length βr) ++ " β-rules\n"))
           _ ← putStrLn (toCostring "Parsing source file ...")
           num_tokens ← return (length (words src))
           just (term , rest) ← return (computation (tr , ∋r , er) empty src)
             where nothing → putStrLn (toCostring "Failed to parse source code file.")
           _ ← putStrLn (toCostring ("term parsed: " ++ print term))
           _ ← putStrLn (toCostring ("ignored: " ++ rest ++ "\n"))
           succeed type ← return (infer rules ε term)
             where fail msg → putStrLn (toCostring msg)
           _ ← putStrLn (toCostring ("term: " ++ (print term) ++ "\ntype: " ++ print type)) 
           return tt
-}

  open import Rules using (∋rule; TypeRule; ε; _⇉_; type; _⊢'_; _placeless)
  open import Pattern using (Pattern; `; _∙_; bind; place; ∙_; _∙; ⋆)
  open import Expression using (`)
  open import Data.List using (_∷_; [])
  open import Thinning using (ι)
  open ∋rule
  open TypeRule
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

  r : ∋rule
  subject r = ` "lam" ∙ bind (` "->" ∙ (place ι))
  input r = subject t
  premises r = input r ∙ bind (place ι) , ((` "" ⊢' type (∙ bind (∙ ⋆)) ι) ⇉ ε ((` "lam" ∙ bind (` "->" ∙ (place ι))) placeless))

  fake : TypeRule
  subject  fake = place ι
  premises fake = ` "⊤" ∙ place ι , type ⋆ ι ⇉ ε (` "⊤" placeless)

  rules : Rules
  rules = (t ∷ t' ∷ [] , r ∷ r' ∷ [] , [])

  ans1 = construction 4 rules {0} empty "lam x -> x"
  ans2 = construction 3 rules {0} empty "alpha -> alpha"  
  ans = computation rules {0} empty "(lam x -> x : alpha -> alpha) "
  
  ans4 = construction 1 rules {0} empty "alpha"  

  import Parser
  open Parser.Parsers using (all-of)
  checker = all-of (lmap (λ tp → tp 3 rules {0} empty) (const-parsers rules)) "alpha -> alpha"
