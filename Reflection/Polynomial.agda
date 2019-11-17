module Reflection.Polynomial where

open import Reflection.Expr

open import Data.List as List using (List)
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec using (Vec)

AddMul : System
AddMul = array 2 (2 Vec.∷ 2 Vec.∷ Vec.[])

_+₀_ : {A : Set} → A → A → Operator AddMul A
x +₀ y = buildOp Fin.zero (x Vec.∷ y Vec.∷ Vec.[])

_*₀_ : {A : Set} → A → A → Operator AddMul A
x *₀ y = buildOp (Fin.suc Fin.zero) (x Vec.∷ y Vec.∷ Vec.[])

Polynomial : ℕ → System
Polynomial = extend AddMul

_+_ : {n : ℕ} {A : Set} →
  Expr (Polynomial n) → Expr (Polynomial n) → Expr (Polynomial n)
x + y = fromOp (injectOp (x +₀ y))

_*_ : {n : ℕ} {A : Set} →
  Expr (Polynomial n) → Expr (Polynomial n) → Expr (Polynomial n)
x * y = fromOp (injectOp (x *₀ y))

