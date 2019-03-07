open import Data.Nat as ℕ using (ℕ; _*_; _+_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

data _or_ (A B : Set) : Set where
  inl : A → A or B
  inr : B → A or B

theorem : ∀ (n : ℕ) → ∃[ r ] ((n ≡ r * 2) or (n ≡ 1 + r * 2))
-- if n = 0 then 0 = 0 * 2 => n even
theorem ℕ.zero = ℕ.zero , inl refl
-- if n > 0 then relabel as (1 + n)
theorem (ℕ.suc n) with theorem n
-- if n is even then 1 + n is odd
-- i.e. n = r * 2 => 1 + n = 1 + r * 2
... | r , inl n-even = r , inr (cong (1 +_) n-even)
-- if n is odd then 1 + n is even
-- i.e. n = 1 + r * 2 => 1 + n = 2 + r * 2 = (1 + r) * 2
... | r , inr n-odd = ℕ.suc r , inl (cong (1 +_) n-odd)

dec-even : ∀ (n : ℕ) → Dec (∃[ r ] (n ≡ r * 2))
dec-even n with theorem n
dec-even n | r , inl n-even = yes (r , n-even)
dec-even n | r , inr n-odd = no λ n-even → ? -- even-contradicts-odd
