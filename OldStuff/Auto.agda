open import Data.Nat
open import Relation.Binary.PropositionalEquality

assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c
assoc zero b c = refl
assoc (suc a) b c = cong suc (assoc a b c)
