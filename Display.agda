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
