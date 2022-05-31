open import Data.Empty using (⊥)
open import Data.Empty.Irrelevant using (⊥-elim)

open import Relation.Binary.PropositionalEquality

record Not (A : Set) : Set where
  constructor not
  field
    .proof : A → ⊥

absurd : {A B : Set} → Not A → A → B
absurd (not f) x = ⊥-elim (f x)

isProp : {A : Set} → {x y : Not A} → x ≡ y
isProp = refl
