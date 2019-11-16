module Reflection.Polynomial where

open import Reflection.Expr

open import Data.List as List using (List)
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec using (Vec)

Polynomial : ℕ → System
Polynomial n = array (2 ℕ.+ n) (2 Vec.∷ 2 Vec.∷ Vec.replicate 0)

_⟨+⟩_ : {n : ℕ} {A : Set} → A → A → Operator (Polynomial n) A
_⟨+⟩_ {n} {A} x y = record { id = Fin.zero; arguments = x Vec.∷ y Vec.∷ Vec.[] }

_⟨*⟩_ : {n : ℕ} {A : Set} → A → A → Operator (Polynomial n) A
_⟨*⟩_ {n} {A} x y = record { id = Fin.suc Fin.zero; arguments = x Vec.∷ y Vec.∷ Vec.[] }

⟨~⟩_ : {n : ℕ} {A : Set} → Fin n → Operator (Polynomial n) A
⟨~⟩_ {n} {A} i = record { id = Fin.raise 2 i; arguments = empty i } where
  empty : {m : ℕ} → (i : Fin m) → Vec A (Vec.lookup i (Vec.replicate 0))
  empty Fin.zero = Vec.[]
  empty (Fin.suc i) = empty i

_+_ : {n : ℕ} {A : Set} →
  Expr (Polynomial n) → Expr (Polynomial n) → Expr (Polynomial n)
x + y = Expr.fromOp (x ⟨+⟩ y)

_*_ : {n : ℕ} {A : Set} →
  Expr (Polynomial n) → Expr (Polynomial n) → Expr (Polynomial n)
x * y = Expr.fromOp (x ⟨*⟩ y)

~_ : {n : ℕ} {A : Set} → Fin n → Expr (Polynomial n)
~ i = Expr.fromOp (⟨~⟩ i)


