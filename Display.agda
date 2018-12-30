open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

import Untyped

data OpenTerm (n : ℕ) : Set where
  Apply : OpenTerm n → OpenTerm n → OpenTerm n
  Lambda : OpenTerm (ℕ.suc n) → OpenTerm n
  Var : Fin n → OpenTerm n

  repeat : ℕ → OpenTerm n
  choose : ℕ → OpenTerm n
  tuple : ℕ → OpenTerm n
  inj : ℕ → ℕ → OpenTerm n

open OpenTerm

fromUntyped : ∀ {n : ℕ} → Untyped.OpenTerm n → OpenTerm n
fromUntyped (Untyped.OpenTerm.Apply x y) =
  Apply (fromUntyped x) (fromUntyped y)
fromUntyped (Untyped.OpenTerm.Lambda m) = Lambda (fromUntyped m)
fromUntyped (Untyped.OpenTerm.Var i) = Var i

toUntyped : ∀ {n : ℕ} → OpenTerm n → Untyped.OpenTerm n
toUntyped (Apply x y) =
  Untyped.OpenTerm.Apply (toUntyped x) (toUntyped y)
toUntyped (Lambda m) = Untyped.OpenTerm.Lambda (toUntyped m)
toUntyped (Var i) = Untyped.OpenTerm.Var i

toUntyped (repeat k) = Untyped.repeat k
toUntyped (choose k) = Untyped.choose k
toUntyped (tuple k) = Untyped.tuple k
toUntyped (inj n k) = ? -- Untyped.inj n k


raise : (n k : ℕ) → OpenTerm n → OpenTerm (k Data.Nat.+ n)
raise n k term = ?
inject : (n k : ℕ) → OpenTerm n → OpenTerm (k Data.Nat.+ n)
inject n k term = ?


_contains_ : {n : ℕ} → OpenTerm n → Fin n → Bool
term contains i = ?

head-normalize : {n : ℕ} → OpenTerm n → OpenTerm n
head-normalize term = ?

-- Eta normalization

-- λx.Mx => M
check-eta : {n : ℕ} → OpenTerm n → Bool
check-eta term = ?
apply-eta : {n : ℕ} → OpenTerm n → OpenTerm n
apply-eta term = ?

-- λx.M => const 1 M
check-const1 : {n : ℕ} → OpenTerm n → Bool
check-const1 term = ?
apply-const1 : {n : ℕ} → OpenTerm n → OpenTerm n
apply-const1 term = ?
-- const i (const j M) => const (i + j) M
check-const+ : {n : ℕ} → OpenTerm n → Bool
check-const+ term = ?
apply-const+ : {n : ℕ} → OpenTerm n → OpenTerm n
apply-const+ term = ?
-- const i (λf.const j (f M)) => inj (i + j + 1) (i + 1) M
-- note that const 0 would be omitted, which must be accounted for
-- inj 1 1 = tuple 1 though perhaps both should be explicitly ignored
check-inj1 : {n : ℕ} → OpenTerm n → Bool
check-inj1 term = ?
apply-inj1 : {n : ℕ} → OpenTerm n → OpenTerm n
apply-inj1 term = ?
-- const i (inj n j M) => inj (n + i) (j + i) M
-- would make the above partly redundant, but above is necessary for preventing
-- inj 1 1 without preventing inj n n
-- may be neater to just check for inj 1 1 better without using the outer const
check-inj+ : {n : ℕ} → OpenTerm n → Bool
check-inj+ term = ?
apply-inj+ : {n : ℕ} → OpenTerm n → OpenTerm n
apply-inj+ term = ?
-- (λf.fM_0..M_n) => tuple n M_0 .. M_n
check-tuple : {n : ℕ} → OpenTerm n → Bool
check-tuple term = ?
apply-tuple : {n : ℕ} → OpenTerm n → OpenTerm n
apply-tuple term = ?
-- λx.repeat n f (f M) => λx.repeat (n+1) f M
-- requires normalizing in tail position
-- also remember that (repeat 0 f) is implicit but repeat 1 f should be avoided
-- finally only variables should be collected into repeat, since the only goal
-- is to eta reduce λfx.repeat n f x down to repeat n
check-repeat : {n : ℕ} → OpenTerm n → Bool
check-repeat term = ?
apply-repeat : {n : ℕ} → OpenTerm n → OpenTerm n
apply-repeat term = ?

-- this detects places where builtins could be used, and does a transformation
-- equivalent to a beta expansion followed by eta reduction, so it feels like
-- "eta normalization" after a while
eta-normalize : {n : ℕ} → OpenTerm n → OpenTerm n
eta-normalize term = ?

