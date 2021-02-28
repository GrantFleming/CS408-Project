module Test.ParserTest where
  open import SpecParser
  open import IO
  open import TypeChecker using (RuleSet)
  open import Data.Maybe using (Maybe; just; nothing) renaming (maybe′ to maybe)
  open import Failable hiding (_>>=_; return) renaming (fail to ffail)
  open import Rules using (∋rule)
  open import Semantics using (β-rule)

  spec : String
  spec = "value: a"

  test : Maybe ((∋rule × List (β-rule)) × String)
  test = value (` "alpha") empty [] spec
