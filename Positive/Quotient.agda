module Positive.Quotient where

open import Positive.Natural as ℕ⁺ using (ℕ⁺)
  renaming (_+_ to _⟨+⟩_; _*_ to _⟨*⟩_)

record ℚ⁺ : Set where
  constructor _:/_
  field
    num : ℕ⁺
    denom : ℕ⁺

fromNat : ℕ⁺ → ℚ⁺
fromNat x = x :/ ℕ⁺.fromℕ 1

_+_ : ℚ⁺ → ℚ⁺ → ℚ⁺
(n₁ :/ d₁) + (n₂ :/ d₂) =
  ((n₁ ⟨*⟩ d₂) ⟨+⟩ (n₂ ⟨*⟩ d₁)) :/ (d₁ ⟨*⟩ d₂)

_*_ : ℚ⁺ → ℚ⁺ → ℚ⁺
(n₁ :/ d₁) * (n₂ :/ d₂) = (n₁ ⟨*⟩ n₂) :/ (d₁ ⟨*⟩ d₂)

invert : ℚ⁺ → ℚ⁺
invert (n :/ d) = d :/ n

_/_ : ℚ⁺ → ℚ⁺ → ℚ⁺
x / y = x * invert y

_==1 : ℚ⁺ → Set
(n :/ d) ==1 = n ≡ d

_==_ : ℚ⁺ → ℚ⁺ → Set
x == y = (x / y) ==1

module properties where
  open import Relation.Binary.PropositionalEquality
  dist : {a b c : ℚ⁺} → (a * (b + c)) == ((a * b) + (a * c))
