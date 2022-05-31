open import CoreInterface using (BoolCore)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec)

module Theorem (Bool : Set) (boolCore : BoolCore Bool) where

true = BoolCore.true boolCore
false = BoolCore.false boolCore
elim = BoolCore.elim boolCore
β₁ = BoolCore.β₁ boolCore
β₂ = BoolCore.β₂ boolCore

if_then_else_ : {A : Set} → Bool → A → A → A
if_then_else_ {A} b x y = elim {λ b → A} x y b

η : ∀ (x : Bool) → (if x then true else false) ≡ x
η = elim {λ x → (if x then true else false) ≡ x} (β₁ true false) (β₂ true false)

--exc-middle : ∀ (b : Bool) → b ≡ true /\ b ≡ false

data IsTrue : Bool → Set where
  trefl : IsTrue true

decTrue : ∀ (b : Bool) → Dec (IsTrue b)
decTrue b = elim (λ b → Dec (IsTrue b)) (Dec.yes trefl) (Dec.no λ())

