module Reflection.Semigroup where

open import Reflection.Expr
open import Reflection.Equation

open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.Vec.Functional as Vector using (Vector; _∷_; [])
open import Data.List as List using (List)

Op₂ : Set → Set
Op₂ A = A → A → A

magma : System
magma = system 0 0 1

magmaEval : ∀ {M n} → (_•_ : Op₂ M) → Expr magma n → Vector M n → M
magmaEval _•_ = evaluate [] [] (_•_ ∷ [])

_•_ : ∀ {n} → Op₂ (Expr magma n)
_•_ = binary Fin.zero

assoc-raw : BasisEquation magma
assoc-raw = ((a • b) • c) :≈ (a • (b • c)) where
  a = var Fin.zero
  b = var (Fin.suc Fin.zero)
  c = var (Fin.suc (Fin.suc Fin.zero))

_≈_ : ∀ {n} → ExprRel magma n
_≈_ {n} = Derivation {magma} {1} (assoc-raw ∷ []) n

