module Monads where

open import Data.Product



module State where

  State : Set → Set → Set
  State s a = s → (a × s)

  return : forall {S A} → A → State S A
  return a = λ s → a , s

  _>>_ : ∀ {S A B} → State S A → State S B → State S B
  _>>_ m k s = k (proj₂ (m s))

  _>>=_ : ∀ {S A B} → State S A → (A → State S B) → State S B
  _>>=_ m k s = k (proj₁ (m s)) (proj₂ (m s))




module Maybe where

  private
    variable
      A B : Set

  data Maybe (A : Set): Set where
    just : A → Maybe A
    nothing : Maybe A

  return : A → Maybe A
  return a = just a

  _>>_ : Maybe A → Maybe B → Maybe B
  just x >> k  = k
  nothing >> k = nothing

  _>>=_ : Maybe A → (A → Maybe B) → Maybe B
  just x >>= k  = k x
  nothing >>= k = nothing




module StateMaybe where

  open Maybe using (Maybe; just; nothing)
  open import Data.Unit

  private
    variable
      S A B : Set
      

  StateMaybe : Set → Set → Set
  StateMaybe s a = s → Maybe (a × s)

  return : A → StateMaybe S A
  return a = λ s → just (a , s)

  _>>=_ : StateMaybe S A → (A → StateMaybe S B) → StateMaybe S B
  _>>=_ m k s with m s
  ... | just (a , s′) = k a s′
  ... | nothing       = nothing

  _>>_ : StateMaybe S A → StateMaybe S B → StateMaybe S B
  m >> k = m >>= λ _ → k
  
  infixl 1 _>>=_
  infixl 1 _>>_

  get : StateMaybe S S
  get s = just (s , s)

  put : S → StateMaybe S ⊤
  put s s′ = just (tt , s)

