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
  constructor buildOp
  field
    id : Fin (Array.length sys)
    arguments : Vec A (Vec.lookup id (Array.content sys))

record Expr (sys : System) : Set where
  inductive
  constructor fromOp
  field
    toOp : Operator sys (Expr sys)

extend : System → ℕ → System
extend (array len rs) n = array (len ℕ.+ n) (rs Vec.++ Vec.replicate 0)

injectLemma : ∀ {m n} {A : Set} {xs : Vec A m} {ys : Vec A n} →
  ∀ (i : Fin m) (C : A → Set) →
  C (Vec.lookup i xs) → C (Vec.lookup (Fin.inject+ n i) (xs Vec.++ ys))
injectLemma {xs = _ Vec.∷ _} Fin.zero C z = z
injectLemma {ℕ.suc m} {xs = _ Vec.∷ xs} (Fin.suc i) C z = injectLemma i C z

injectOp : {sys : System} {n : ℕ} {A : Set} →
  Operator sys A → Operator (extend sys n) A
injectOp {sys} {n} {A} (buildOp id args) =
  buildOp (Fin.inject+ n id) (injectLemma id (Vec A) args)

{-# TERMINATING #-}
inject : {sys : System} → {n : ℕ} → Expr sys → Expr (extend sys n)
inject (fromOp (buildOp id args)) =
  fromOp (injectOp (buildOp id (Vec.map inject args)))

raiseLemma : ∀ {m n} {A : Set} {xs : Vec A m} {ys : Vec A n} →
  ∀ (i : Fin n) (C : A → Set) →
  C (Vec.lookup i ys) → C (Vec.lookup (Fin.raise m i) (xs Vec.++ ys))
raiseLemma {ℕ.zero} {xs = Vec.[] } i C z = z
raiseLemma {ℕ.suc m} {xs = _ Vec.∷ _} i C z = raiseLemma {m} i C z

varOp : {sys : System} {n : ℕ} {A : Set} →
  Fin n → Operator (extend sys n) A
varOp {array len _} {n} {A} i =
  buildOp (Fin.raise len i) (raiseLemma {len} {n} {ℕ} i (Vec A) (empty i)) where
    empty : {m : ℕ} → (i : Fin m) → Vec A (Vec.lookup i (Vec.replicate 0))
    empty Fin.zero = Vec.[]
    empty (Fin.suc i) = empty i

var : {sys : System} {n : ℕ} → Fin n → Expr (extend sys n)
var i = fromOp (varOp i)


