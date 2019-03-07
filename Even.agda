open import Data.Nat as ℕ using (ℕ; _*_; _+_)
open import Data.Product
open import Data.Empty as ⊥ using (⊥)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

Even : ℕ → Set
Even n = ∃[ r ] (n ≡ r * 2)

Odd : ℕ → Set
Odd n = ∃[ r ] (n ≡ 1 + r * 2)

data EvenOrOdd (n : ℕ) : Set where
  even : Even n → EvenOrOdd n
  odd : Odd n → EvenOrOdd n

even-step : ∀ {n : ℕ} → Even n → Odd (1 + n)
-- n = r*2 => 1 + n = 1 + r*2
even-step (r , refl) = r , refl

even-back : ∀ {n : ℕ} → Even (1 + n) → Odd n
-- 1 + n /= 0
even-back (ℕ.zero , ())
--    1 + n = (1 + r) * 2 = 2 + r * 2
-- => n = 1 + r * 2
even-back (ℕ.suc r , suc-even) = r , cong ℕ.pred suc-even

odd-step : ∀ {n : ℕ} → Odd n → Even (1 + n)
--    n = 1 + r*2
-- => 1 + n = 2 + r*2 = (1 + r)*2
odd-step (r , refl) = 1 + r , refl

odd-back : ∀ {n : ℕ} → Odd (1 + n) → Even n
--    1 + n = 1 + r * 2
-- => n = r * 2
odd-back (r , suc-odd) = r , cong ℕ.pred suc-odd

-- if you know whether n is even then you know whether 1 + n is even
decide-step : ∀ {n : ℕ} → EvenOrOdd n → EvenOrOdd (1 + n)
decide-step (even prf) = odd (even-step prf)
decide-step (odd prf) = even (odd-step prf)

decide : ∀ (n : ℕ) → EvenOrOdd n
-- if n = 0 then 0 = 0 * 2 => n even
decide ℕ.zero = even (0 , refl)
-- if n > 0 then relabel as (1 + n′) and recurse (POMI)
decide (ℕ.suc n′) = decide-step (decide n′)

contradict : ∀ (n : ℕ) → Even n → Odd n → ⊥
-- zero can't be both even and odd because it isn't odd
contradict ℕ.zero p₁ ()
-- suppose 1 + n is even and odd => n is even and odd => contradiction (IH)
contradict (ℕ.suc n) p-e p-o = contradict n (odd-back p-o) (even-back p-e)

dec-even : ∀ (n : ℕ) → Dec (Even n)
dec-even n with decide n
dec-even n | even p-e = yes p-e
dec-even n | odd p-o = no λ p-e → contradict n p-e p-o

dec-odd : ∀ (n : ℕ) → Dec (Odd n)
dec-odd n with decide n
dec-odd n | even p-e = no λ p-o → contradict n p-e p-o
dec-odd n | odd p-o = yes p-o

