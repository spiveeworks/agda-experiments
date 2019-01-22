open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-suc; +-comm)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

resp+-suc : (F : ℕ → Set) → (n m : ℕ) → F (n + ℕ.suc m) → F (ℕ.suc n + m)
resp+-suc F n m = PropEq.subst F (+-suc n m)

resp+-suc′ : (F : ℕ → Set) → (n m : ℕ) → F (ℕ.suc n + m) → F (n + ℕ.suc m)
resp+-suc′ F n m = PropEq.subst F (PropEq.sym (+-suc n m))

resp+-comm : (F : ℕ → Set) → (n m : ℕ) → F (n + m) → F (m + n)
resp+-comm F n m = PropEq.subst F (+-comm n m)

resp+0 : (F : ℕ → Set) → (n : ℕ) → F (n + 0) → F n
resp+0 F n = resp+-comm F n 0

