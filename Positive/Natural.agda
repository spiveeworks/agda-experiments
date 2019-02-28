module Positive.Natural where

open import Data.Nat as ℕ using (ℕ)

data ℕ⁺ : Set where
  suc : ℕ → ℕ⁺

intoℕ : ℕ⁺ → ℕ
intoℕ (suc n) = ℕ.suc n

fromℕ : ℕ → ℕ⁺
fromℕ n = suc (ℕ.pred n)

module eqProp where
  open import Relation.Binary.PropositionalEquality
  prop : ∀ {x : ℕ⁺} → x ≡ fromℕ (intoℕ x)
  prop {suc _} = refl

map₂ : (ℕ → ℕ → ℕ) → (ℕ⁺ → ℕ⁺ → ℕ⁺)
map₂ _*_ x y = fromℕ (intoℕ x * intoℕ y)

_+_ : ℕ⁺ → ℕ⁺ → ℕ⁺
_+_ = map₂ ℕ._+_

_*_ : ℕ⁺ → ℕ⁺ → ℕ⁺
_*_ = map₂ ℕ._*_

module mapProps where
  open import Relation.Binary.PropositionalEquality

  prop+ : {x y : ℕ} → suc x + suc y ≡ suc (x ℕ.+ ℕ.suc y)
  prop+ = refl

  prop* : {x y : ℕ} → suc x * suc y ≡ suc (y ℕ.+ x ℕ.* ℕ.suc y)
  prop* = refl


