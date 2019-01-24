open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-suc; +-comm)
open import Data.Vec
open import Relation.Binary.PropositionalEquality

resp+-suc : (F : ℕ → Set) → (n m : ℕ) → F (n + ℕ.suc m) → F (ℕ.suc n + m)
resp+-suc F n m = subst F (+-suc n m)

resp+-suc′ : (F : ℕ → Set) → (n m : ℕ) → F (ℕ.suc n + m) → F (n + ℕ.suc m)
resp+-suc′ F n m = subst F (sym (+-suc n m))

resp+-comm : (F : ℕ → Set) → (n m : ℕ) → F (n + m) → F (m + n)
resp+-comm F n m = subst F (+-comm n m)

resp+0 : (F : ℕ → Set) → (n : ℕ) → F (n + 0) → F n
resp+0 F n = resp+-comm F n 0


-- equivalent to resp+-suc (Vec T) x y (l ++ (v ∷ r))
-- but with easier type checking (branch on the vec instead of its size)
_<++_++>_ : {x y : ℕ} {T : Set} → Vec T x → T → Vec T y → Vec T (1 + x + y)
[] <++ v ++> r = v ∷ r
(x ∷ l) <++ v ++> r = x ∷ (l <++ v ++> r)

