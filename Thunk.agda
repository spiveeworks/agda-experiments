open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Vec as Vec
open Vec

data OpenExpr (n : ℕ) : Set where
  Apply : OpenExpr n → OpenExpr n → OpenExpr n
  Thunk : {m : ℕ} → Vec (OpenExpr n) m → OpenExpr (ℕ.suc m) → OpenExpr n
  Var : Fin n → OpenExpr n

data Expr : Set where
  Thunk : {n : ℕ} → Vec Expr n → OpenExpr (ℕ.suc n) → Expr


apply : Expr → Expr → Expr
eval : {n : ℕ} → Vec Expr n → OpenExpr n → Expr
{-# NON_TERMINATING #-}
apply (Thunk vars alg) val = eval (val ∷ vars) alg
eval vars (OpenExpr.Apply x y) = apply (eval vars x) (eval vars y)
eval vars (OpenExpr.Thunk ovars alg) = Expr.Thunk (map (eval vars) ovars) alg
eval vars (OpenExpr.Var n) = lookup n vars


