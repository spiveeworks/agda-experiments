
open import Relation.Nullary
open import Data.Empty.Irrelevant
open import Relation.Binary.PropositionalEquality using (_≡_)

fromIrrel : ∀ {l} {A : Set l} → .A → ¬ ¬ A
fromIrrel irrx nx = ⊥-elim (nx irrx)

irrefExt : ∀ {l} {A : Set l} {f g : ¬ ¬ A} → ∀ {x} → f x ≡ g x
irrefExt {f = f} {x = x} = ⊥-elim (f x)

