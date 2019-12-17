module Reflection.Equation where

open import Reflection.Expr

import RelExt
open RelExt.EquivExt using (EquivExt)

open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.Vec.Functional as Vector using (Vector)
open import Relation.Binary as Rel using (Rel)

Eq : (sys : System) → Set₁
Eq sys = Rel (Expr sys) _

data BasisEquation (sys : System) (n m : ℕ) (x y : Expr (extend sys n)) :
  Eq (extend sys m) where
  intro :
    (f : Expr (extend (extend sys m) 1)) →
    (xs : Vector (Expr (extend sys m)) n) →
    BasisEquation sys n m x y (apply f (compose x xs)) (apply f (compose y xs))

record BasisEquationData (sys : System) : Set where
  constructor law
  field
    vars : ℕ
    lhs : Expr (extend sys vars)
    rhs : Expr (extend sys vars)

eqFromExprs : (sys : System) → BasisEquationData sys → ∀ m → Eq (extend sys m)
eqFromExprs sys (law n lhs rhs) m = BasisEquation sys n m lhs rhs

record DerivationRaw {sys : System} {numLaws : ℕ}
  (laws : Vector (BasisEquationData sys) numLaws)
  (m : ℕ) (x y : Expr (extend sys m)) : Set where
  constructor raw
  field
    i : Fin numLaws
    prf : eqFromExprs sys (laws i) m x y

Derivation : {sys : System} {numLaws : ℕ} →
  Vector (BasisEquationData sys) numLaws → (m : ℕ) → Eq (extend sys m)
Derivation laws m = EquivExt (DerivationRaw laws m)

