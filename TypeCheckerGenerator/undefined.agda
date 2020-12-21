module undefined where

postulate undefined : ∀ {a} {A : Set a} → A
{-# COMPILE GHC undefined = undefined #-}