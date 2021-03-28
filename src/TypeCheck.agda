module TypeCheck where

  open import TypeChecker using (RuleSet; rs; infer)
  open import CoreLanguage
  open import IO
  import IO.Primitive as Prim
  open import Codata.Musical.Costring  
  open import Data.Unit.Polymorphic.Base
  open import Data.List using (List; _∷_; []; length)
  open import Data.Bool using (if_then_else_)
  open import Data.Vec using (_∷_)
  open import Data.String using (String; _++_; toList; fromList)
  import SpecParser as SP
  open SP.SpecfileParser using (parse-spec)
  import LanguageParser
  open LanguageParser.LParsers
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Product using (_,_)
  open import Data.Nat.Show using (show)
  open import Data.String.Properties using (<-strictTotalOrder-≈)
  import Data.Tree.AVL.Map as MapMod
  open MapMod <-strictTotalOrder-≈ using (empty)
  open import BwdVec using (ε)
  open import Failable using (succeed; fail)

  postulate
    getArgsRaw    : Prim.IO (List String)
    currentDirRaw : Prim.IO String

  {-# FOREIGN GHC import System.Environment   #-}
  {-# FOREIGN GHC import System.Directory   #-}
  {-# COMPILE GHC getArgsRaw = fmap (map Data.Text.pack) getArgs #-}
  {-# COMPILE GHC currentDirRaw = fmap Data.Text.pack getCurrentDirectory #-}

  getArgs    = lift getArgsRaw
  currentDir = lift currentDirRaw

  relative : String -> Maybe String
  relative str with toList str
  ... | ('/' ∷ rest) = nothing    
  ... | rpath        = just (fromList rpath)

  buildPath : String -> IO String
  buildPath path with relative path
  ... | just rest  = do
                       dir ← currentDir 
                       return (dir ++ "/" ++ rest)
  ... | nothing = return path

  main = run (do
           (desc-filename ∷ source-filename ∷ []) ← getArgs
             where _ → do
                         _ ← putStrLn ("Must supply the name of the specification file" ++
                                       " and the source code file.")
                         return tt
           desc-path ← buildPath desc-filename
           source-path ← buildPath source-filename
           desc ← readFiniteFile desc-path
           src  ← readFiniteFile source-path
           just (rules@(rs tr ur ∋r er βr ηr) , rest) ← return (parse-spec desc)
             where nothing → putStrLn ("Failed to parse spec file")
           _ ← putStrLn ("Parsed:\n" ++ show (length tr) ++ " types\n" ++
                                        show (length ∋r) ++ " values\n" ++
                                        show (length er) ++ " eliminations\n" ++
                                        show (length βr) ++ " β-rules\n")
           just (term , rest) ← return (computation (tr , ∋r , er) empty src)
             where nothing → putStrLn ("Failed to parse source code file.")
           _ ← putStrLn ("Successfully parsed source code file.")           
           _ ← putStrLn ("Term parsed: " ++ print term)
           _ ← putStrLn ("Input ignored: " ++ rest ++ "\n")
           succeed type ← return (infer rules ε term)
             where fail msg → (do
                     _ ← putStrLn("Type checking failed.")
                     putStrLn msg)
           _ ← putStrLn ("Type checking succeeded.")             
           _ ← putStrLn ("type: " ++ print type)
           return tt)

