module Reflection.Expr where

-- blackboard ℕ makes me think it is a subset of ℂ which is bugging me
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec using (Vec)

record Array {l} (A : Set l) : Set l where
  constructor array
  field
    length : ℕ
    content : Vec A length

System : Set
System = Array ℕ

record Operator (sys : System) (A : Set) : Set where
  field
    id : Fin (Array.length sys)
    arguments : Vec A (Vec.lookup id (Array.content sys))

record Expr (sys : System) : Set where
  inductive
  constructor fromOp
  field
    toOp : Operator sys (Expr sys)

