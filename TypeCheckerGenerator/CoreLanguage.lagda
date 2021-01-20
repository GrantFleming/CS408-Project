\section{A core language}

\hide{
\begin{code}
module CoreLanguage where
\end{code}

\begin{code}
open import Data.Nat using (ℕ; suc; zero)
open import Data.Char using (Char)
open import Data.String
\end{code}
}

\begin{code}
Scope = ℕ
Scoped = Scope → Set

data Var : Scope → Set where
  ze : {s : Scope} → Var (suc s)
  su : {s : Scope} → Var s → Var (suc s)

toNum : ∀{γ} → Var γ → ℕ
toNum ze     = 0
toNum (su v) = suc (toNum v)

fromNum : (n : ℕ) → Var (suc n)
fromNum zero = ze
fromNum (suc n) = su (fromNum n)

data Const (γ : Scope) : Set
data Compu (γ : Scope) : Set

data Const γ where
  `      : Char → Const γ
  _∙_    : Const γ → Const γ → Const γ
  bind   : Const (suc γ) → Const γ
  thunk  : Compu γ → Const γ

infixr 20 _∙_ 

data Compu γ where
  var    : Var γ → Compu γ
  elim   : Compu γ → Const γ → Compu γ
  _∷_    : Const γ → Const γ → Compu γ

↠ : ∀ {γ} → Compu γ → Const γ
↠ (t ∷ T) = t
↠  x      = thunk x

data Dir : Set where const compu : Dir

Term : Dir → Scope → Set
Term const γ = Const γ
Term compu γ = Compu γ

private
  variable
    d : Dir
    γ : Scope

print : Term d γ → String
print {const} (` x)      = fromChar x
print {const} (s ∙ t)    = print s ++ print t
print {const} (bind x)   = "λ" ++ print x
print {const} (thunk x)  = "_" ++ print x ++ "_"
print {compu} (var x)    = "VAR"
print {compu} (elim e s) = "elim" ++ print e ++ print s
print {compu} (t ∷ T)    = print t ++ "∶" ++ print T

printrawvar : Var γ → String
printrawvar ze     = "ze"
printrawvar (su v) = "su " ++ printrawvar v

printraw : Term d γ → String
printraw {const} (` x)       = "(` '" ++ fromChar x ++ "')"
printraw {const} (s ∙ t)     = "(" ++ printraw s ++ " ∙ "  ++ printraw t ++ ")"
printraw {const} (bind x)    = "(bind " ++ printraw x ++ ")"
printraw {const} (thunk x)   = "(thunk " ++ printraw x ++ ")"
printraw {compu} (var x)     = "(var " ++ printrawvar x ++ ")"
printraw {compu} (elim e s)  = "(elim " ++ printraw e ++ " " ++ printraw s ++ ")"
printraw {compu} (t ∷ T)     = "(" ++ printraw t ++ "∶" ++ printraw T ++ ")"
\end{code}
