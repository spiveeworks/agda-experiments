open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open import Function using (_∘_)

open import Relation.Nullary using (Dec)

import Untyped
import Church
import EqProps

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

toUntyped (repeat k) = Church.repeat k
toUntyped (choose k) = Church.choose k
toUntyped (tuple k) = Church.tuple k
toUntyped (inj n k) = ? -- Church.inj n k

resp+-suc : (n m : ℕ) → OpenTerm (n Data.Nat.+ ℕ.suc m) →
  OpenTerm (ℕ.suc n Data.Nat.+ m)
resp+-suc = EqProps.resp+-suc OpenTerm

raise : (n k : ℕ) → OpenTerm n → OpenTerm (k Data.Nat.+ n)
raise n k (Apply f x) = Apply (raise n k f) (raise n k x)
raise n k (Lambda body) = Lambda (resp+-suc k n (raise (ℕ.suc n) k body))
raise n k (Var x) = Var (Data.Fin.raise k x)
raise _ _ (repeat n) = repeat n
raise _ _ (choose i) = choose i
raise _ _ (tuple n) = tuple n
raise _ _ (inj n i) = inj n i

inject : (n k : ℕ) → OpenTerm n → OpenTerm (n Data.Nat.+ k)
inject n k (Apply f x) = Apply (inject n k f) (inject n k x)
inject n k (Lambda body) = Lambda (inject (ℕ.suc n) k body)
inject n k (Var x) = Var (Data.Fin.inject+ k x)
inject _ _ (repeat n) = repeat n
inject _ _ (choose i) = choose i
inject _ _ (tuple n) = tuple n
inject _ _ (inj n i) = inj n i

eqb : ℕ → ℕ → Bool
eqb x y = is-yes (x Data.Nat.≟ y) where
  is-yes : {P : Set} → Dec P → Bool
  is-yes (Dec.yes _) = true
  is-yes (Dec.no _) = false

_contains_ : {n : ℕ} → OpenTerm n → ℕ → Bool
Apply f x contains i = (f contains i) ∨ (x contains i)
Lambda body contains i = body contains i
Var x contains i = eqb (Data.Fin.toℕ x) i
repeat x contains i = false
choose x contains i = false
tuple x contains i = false
inj x x₁ contains i = false

head-normalize : {n : ℕ} → OpenTerm n → OpenTerm n
head-normalize term = term

-- Eta normalization

-- λx.Mx => M
check-eta : {n : ℕ} → OpenTerm n → Bool
check-eta term = false
apply-eta : {n : ℕ} → OpenTerm n → OpenTerm n
apply-eta term = term

-- λx.M => const 1 M
check-const1 : {n : ℕ} → OpenTerm n → Bool
check-const1 term = false
apply-const1 : {n : ℕ} → OpenTerm n → OpenTerm n
apply-const1 term = term
-- const i (const j M) => const (i + j) M
check-const+ : {n : ℕ} → OpenTerm n → Bool
check-const+ term = false
apply-const+ : {n : ℕ} → OpenTerm n → OpenTerm n
apply-const+ term = term
-- const i (λf.const j (f M)) => inj (i + j + 1) (i + 1) M
-- note that const 0 would be omitted, which must be accounted for
-- inj 1 1 = tuple 1 though perhaps both should be explicitly ignored
check-inj1 : {n : ℕ} → OpenTerm n → Bool
check-inj1 term = false
apply-inj1 : {n : ℕ} → OpenTerm n → OpenTerm n
apply-inj1 term = term
-- const i (inj n j M) => inj (n + i) (j + i) M
-- would make the above partly redundant, but above is necessary for preventing
-- inj 1 1 without preventing inj n n
-- may be neater to just check for inj 1 1 better without using the outer const
check-inj+ : {n : ℕ} → OpenTerm n → Bool
check-inj+ term = false
apply-inj+ : {n : ℕ} → OpenTerm n → OpenTerm n
apply-inj+ term = term
-- (λf.fM_0..M_n) => tuple n M_0 .. M_n
check-tuple : {n : ℕ} → OpenTerm n → Bool
check-tuple term = false
apply-tuple : {n : ℕ} → OpenTerm n → OpenTerm n
apply-tuple term = term
-- λx.repeat n f (f M) => λx.repeat (n+1) f M
-- requires normalizing in tail position
-- also remember that (repeat 0 f) is implicit but repeat 1 f should be avoided
-- finally only variables should be collected into repeat, since the only goal
-- is to eta reduce λfx.repeat n f x down to repeat n
check-repeat : {n : ℕ} → OpenTerm n → Bool
check-repeat term = false
apply-repeat : {n : ℕ} → OpenTerm n → OpenTerm n
apply-repeat term = term

-- note that the const1 needs to come before other const/inj based checks
-- and eta needs to come after things that dont remove lambdas such as repeat
apply-all : {n : ℕ} → OpenTerm n → OpenTerm n
apply-all = apply-eta ∘ apply-repeat ∘ apply-tuple ∘ apply-inj+ ∘ apply-inj1 ∘
  apply-const+ ∘ apply-const1

-- this detects places where builtins could be used, and does a transformation
-- equivalent to a beta expansion followed by eta reduction, so it feels like
-- "eta normalization" after a while
eta-normalize : {n : ℕ} → OpenTerm n → OpenTerm n
eta-normalize-loop : {n : ℕ} → OpenTerm n → OpenTerm n
eta-normalize-inner : {n : ℕ} → OpenTerm n → OpenTerm n
{-# NON_TERMINATING #-}
eta-normalize = eta-normalize-loop ∘ head-normalize
eta-normalize-loop = apply-all ∘ eta-normalize-inner
eta-normalize-inner (Lambda term) = Lambda (eta-normalize-loop term)
eta-normalize-inner (Apply f@(choose _) x) = Apply f (eta-normalize x)
eta-normalize-inner term = term

