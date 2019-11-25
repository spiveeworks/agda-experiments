
data Void : Set where

data Undef : Set where
  intro : Undef -> Undef

absurd : Undef -> Void
absurd (intro x) = absurd x

