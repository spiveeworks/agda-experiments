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


_<++_++>_ : {x y : ℕ} {T : Set} → Vec T x → T → Vec T y → Vec T (1 + x + y)
l <++ v ++> r = resp+-suc (Vec _) _ _ (l ++ (v ∷ r))

concatLemma : {ln rn : ℕ} {T : Set} → ∀(x : T)(l : Vec T ln)(r : Vec T rn) →
  (x ∷ (l ++ r)) ≡ ((x ∷ l) ++ r)
concatLemma x l r = ?

concatLemma′ : {ln rn : ℕ} {T : Set} → ∀(x v : T)(l : Vec T ln)(r : Vec T rn) →
  (x ∷ (l <++ v ++> r)) ≡ ((x ∷ l) <++ v ++> r)
concatLemma′ x v l r = ? (concatLemma x l (v ∷ r))

respConcat : {ln rn : ℕ} {T : Set} → ∀(x v : T)(l : Vec T ln)(r : Vec T rn) →
  ∀(F : (Vec T (2 + ln + rn)) → Set) →
    F (x ∷ (l <++ v ++> r)) → F ((x ∷ l) <++ v ++> r)
respConcat x v l r F = subst F (concatLemma′ x v l r)

respConcat′ : {ln rn : ℕ} {T : Set} → ∀(x v : T)(l : Vec T ln)(r : Vec T rn) →
  ∀(F : (Vec T (2 + ln + rn)) → Set) →
    F ((x ∷ l) <++ v ++> r) → F (x ∷ (l <++ v ++> r))
respConcat′ x v l r F = subst F (sym (concatLemma′ x v l r))
