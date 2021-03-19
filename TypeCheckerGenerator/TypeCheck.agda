module TypeCheck where

  open import TypeChecker using (RuleSet; rs; infer)
  open import CoreLanguage
  open import IO
  import IO.Primitive as Prim
  open import Codata.Musical.Costring  
  open import Data.Unit.Polymorphic.Base
  open import Data.List using (List; _∷_; []; length)
  open import Data.Bool using (if_then_else_)
  open import Data.String using (String; _++_)
  import SpecParser as SP
  open SP.SpecfileParser using (parse-spec)
  import LanguageParser
  open LanguageParser.LParsers
  open import Data.Maybe using (just; nothing)
  open import Data.Product using (_,_)
  open import Data.Nat.Show using (show)
  open import Data.String.Properties using (<-strictTotalOrder-≈)
  import Data.Tree.AVL.Map as MapMod
  open MapMod <-strictTotalOrder-≈ using (empty)
  open import BwdVec using (ε)
  open import Failable using (succeed; fail)

  postulate
    getArgsRaw : Prim.IO (List String)

  {-# FOREIGN GHC import System.Environment   #-}
  {-# COMPILE GHC getArgsRaw = fmap (map Data.Text.pack) getArgs #-}

  getArgs = lift getArgsRaw

  main = run (do
           (desc-filename ∷ source-filename ∷ []) ← getArgs
             where _ → do
                         _ ← putStrLn ("Must supply the name of the specification file" ++
                                       " and the source code file.")
                         return tt
           desc ← readFiniteFile desc-filename
           src  ← readFiniteFile source-filename
           just (rules@(rs tr ur ∋r er βr ηr) , rest) ← return (parse-spec desc)
             where nothing → putStrLn ("Failed to parse spec file")
           _ ← putStrLn ("Parsed:\n" ++ show (length tr) ++ " types\n" ++
                                        show (length ∋r) ++ " introduction forms\n" ++
                                        show (length er) ++ " elimination typing rules\n" ++
                                        show (length βr) ++ " β-rules\n")
           _ ← putStrLn ("Parsing source file ...")
           just (term , rest) ← return (computation (tr , ∋r , er) empty src)
             where nothing → putStrLn ("Failed to parse source code file.")
           _ ← putStrLn ("term parsed: " ++ print term)
           _ ← putStrLn ("ignored: " ++ rest ++ "\n")
           succeed type ← return (infer rules ε term)
             where fail msg → putStrLn msg
           _ ← putStrLn ("term: " ++ (print term) ++ "\ntype: " ++ print type)
           return tt)

