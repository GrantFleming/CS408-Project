module Test.ParserTest where
  open import SpecParser
  open SpecParser.ExpressionParser
  open import IO
  open import TypeChecker using (RuleSet)
  open import Data.Maybe using (Maybe; just; nothing) renaming (maybe′ to maybe)
  open import Failable hiding (_>>=_; return) renaming (fail to ffail)
  open import Rules using (∋rule)
  open import Semantics using (β-rule)
  open import Data.String
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Pattern using (`)

