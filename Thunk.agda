open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Vec as Vec
open Vec
open import Function
open import Relation.Binary.PropositionalEquality

open import Untyped

data OpenExpr (n : ℕ) : Set where
  Apply : OpenExpr n → OpenExpr n → OpenExpr n
  Thunk : {m : ℕ} → Vec (OpenExpr n) m → OpenExpr (ℕ.suc m) → OpenExpr n
  Var : Fin n → OpenExpr n

data Expr : Set where
  Thunk : {n : ℕ} → Vec Expr n → OpenExpr (ℕ.suc n) → Expr


apply : Expr → Expr → Expr
eval : {n : ℕ} → Vec Expr n → OpenExpr n → Expr
{-# TERMINATING #-}
apply (Thunk vars alg) val = eval (val ∷ vars) alg
eval vars (OpenExpr.Apply x y) = apply (eval vars x) (eval vars y)
eval vars (OpenExpr.Thunk ovars alg) = Expr.Thunk (map (eval vars) ovars) alg
eval vars (OpenExpr.Var n) = lookup n vars


vars : {n : ℕ} → Vec (OpenExpr n) n
vars = Vec.map OpenExpr.Var (Vec.allFin _)

fromUntyped : {n : ℕ} → OpenTerm n → OpenExpr n
fromUntyped (OpenTerm.Apply x y) =
  OpenExpr.Apply (fromUntyped x) (fromUntyped y)
fromUntyped (OpenTerm.Lambda body) = OpenExpr.Thunk vars (fromUntyped body)
fromUntyped (OpenTerm.Var n) = OpenExpr.Var n

evalUntyped : Term → Expr
evalUntyped = eval [] ∘ fromUntyped

module Tests where
  uid : Term
  uid = OpenTerm.Lambda (OpenTerm.Var Fin.zero)
  tid : Expr
  tid = Expr.Thunk [] (OpenExpr.Var Fin.zero)

  uconst : Term
  uconst = OpenTerm.Lambda (OpenTerm.Lambda (OpenTerm.Var (Fin.suc Fin.zero)))
  tfalse = Expr.Thunk (tid ∷ []) (OpenExpr.Var (Fin.suc Fin.zero))

  testOne : evalUntyped uid ≡ tid
  testOne = refl

  testTwo : evalUntyped (OpenTerm.Apply uconst uid) ≡ tfalse
  testTwo = refl
