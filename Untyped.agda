open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-suc; +-comm)
open import Data.Fin as Fin using (Fin)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

data OpenTerm (n : ℕ) : Set where
  Apply : OpenTerm n → OpenTerm n → OpenTerm n
  Lambda : OpenTerm (ℕ.suc n) → OpenTerm n
  Var : Fin n → OpenTerm n

Term : Set
Term = OpenTerm ℕ.zero

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
  intros {n′} (ℕ.suc m) x = OpenTerm.Lambda (intros m (resp x)) where
    resp : OpenTerm (n′ + ℕ.suc m) → OpenTerm (ℕ.suc n′ + m)
    resp = PropEq.subst OpenTerm (+-suc n′ m)
  intros {n′} ℕ.zero x = resp x where
    resp : OpenTerm (n′ + ℕ.zero) → OpenTerm n′
    resp = PropEq.subst OpenTerm (+-comm n′ ℕ.zero)
  body : OpenTerm (n + ℕ.suc k)
  body = resp (aps varzero fk) where
    resp : OpenTerm (ℕ.suc n + k) → OpenTerm (n + ℕ.suc k)
    resp = PropEq.subst OpenTerm (PropEq.sym (+-suc n k))
    varzero : OpenTerm (ℕ.suc n + k)
    varzero = OpenTerm.Var (Fin.zero)
    fk : Fin (ℕ.suc n + k)
    fk = fresp (Fin.inject+ n (Fin.fromℕ k)) where
      fresp : Fin (ℕ.suc k + n) → Fin (ℕ.suc n + k)
      fresp = PropEq.subst (λ m → Fin (ℕ.suc m)) (+-comm k n)
    aps : {n′ : ℕ} → OpenTerm n′ → Fin n′ → OpenTerm n′
    aps f Fin.zero = f
    aps f x@(Fin.suc x′) = aps (OpenTerm.Apply f (OpenTerm.Var x)) x′′
      where x′′ = Fin.inject₁ x′

