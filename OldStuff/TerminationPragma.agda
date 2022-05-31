{-# NON_TERMINATING #-}
Y : {A : Set} → (A → A) → A
Y f = f (Y f)

id : {A : Set} → A → A
id x = x

absurd : {A : Set} → A
absurd = Y id

