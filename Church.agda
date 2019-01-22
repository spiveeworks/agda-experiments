open import Data.Nat using (ℕ; _+_)
open import Data.Fin as Fin using (Fin)
open import Data.Nat.Properties using (+-suc; +-comm)

open import Untyped
open import EqProps

-- Church terms
-- used in Display.agda

frepeat : {A : Set} → ℕ → (A → A) → (A → A)
frepeat ℕ.zero f x = x
frepeat (ℕ.suc n) f x = f (frepeat n f x)

repeat : {n : ℕ} → ℕ → OpenTerm n
repeat k = OpenTerm.Lambda (OpenTerm.Lambda (frepeat k ap (Var Fin.zero)))
  where ap = OpenTerm.Apply (OpenTerm.Var (Fin.suc Fin.zero))

-- choose? choose 1 x y = x... choose 2 x y = \z.x ??
-- what about drop 1 x y = x, drop 2 x y z = x
choose : {n : ℕ} → ℕ → OpenTerm n
choose k = OpenTerm.Lambda (choose′ k Fin.zero) where
  choose′ : ℕ → {n′ : ℕ} → Fin n′ → OpenTerm n′
  choose′ ℕ.zero i = OpenTerm.Var i
  choose′ (ℕ.suc n) i = OpenTerm.Lambda (choose′ n (Fin.suc i))

-- tuple 2 = λ x y f . f x y
-- λλλ$($02)1
{-# TERMINATING #-}
tuple : {n : ℕ} → ℕ → OpenTerm n
tuple {n} k = intros (ℕ.suc k) body where
  intros : {n′ : ℕ} (m : ℕ) → OpenTerm (n′ + m) → OpenTerm n′
  intros {n′} (ℕ.suc m) x = OpenTerm.Lambda
    (intros m (resp+-suc OpenTerm n′ m x))
  intros {n′} ℕ.zero x = resp+0 OpenTerm _ x
  body : OpenTerm (n + ℕ.suc k)
  body = resp+-suc′ OpenTerm _ _ (aps varzero fk) where
    varzero : OpenTerm (ℕ.suc n + k)
    varzero = OpenTerm.Var (Fin.zero)
    fk : Fin (ℕ.suc n + k)
    fk = fresp (Fin.inject+ n (Fin.fromℕ k)) where
      fresp : Fin (ℕ.suc k + n) → Fin (ℕ.suc n + k)
      fresp = resp+-comm (λ m → Fin (ℕ.suc m)) k n
    aps : {n′ : ℕ} → OpenTerm n′ → Fin n′ → OpenTerm n′
    aps f Fin.zero = f
    aps f x@(Fin.suc x′) = aps (OpenTerm.Apply f (OpenTerm.Var x)) x′′
      where x′′ = Fin.inject₁ x′

