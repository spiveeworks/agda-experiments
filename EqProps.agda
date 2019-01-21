open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-suc; +-comm)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

resp+-suc : (F : ℕ → Set) → (n m : ℕ) → F (n + ℕ.suc m) → F (ℕ.suc n + m)
resp+-suc F n m = PropEq.subst F (+-suc n m)

