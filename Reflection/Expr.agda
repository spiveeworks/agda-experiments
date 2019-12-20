module Reflection.Expr where

-- blackboard ℕ makes it look like it is a subset of ℂ which is bugging me
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.Vec.Functional as Vector using (Vector)

record System : Set where
  constructor system
  field
    constant_num : ℕ -- vector spaces and so on might want infinite constants?
    unary_num : ℕ
    binary_num : ℕ

data Expr (sys : System) (vars : ℕ) : Set where
  var : Fin vars → Expr sys vars
  constant : Fin (System.constant_num sys) → Expr sys vars
  unary : Fin (System.unary_num sys) → Expr sys vars → Expr sys vars
  binary : Fin (System.binary_num sys) → Expr sys vars → Expr sys vars → Expr sys vars

{-
 - Substitution
 -}

compose : {sys : System} → {m n : ℕ} → Expr sys m →
  Vector (Expr sys n) m → Expr sys n
compose {sys} {m} {n} expr vars = recursor expr where
  recursor : Expr sys m → Expr sys n
  recursor (var i) = vars i
  recursor (constant i) = constant i
  recursor (unary i x) = unary i (recursor x)
  recursor (binary i x y) = binary i (recursor x) (recursor y)

evaluate : {c u b v : ℕ} → {A : Set} →
  Vector A c → Vector (A → A) u → Vector (A → A → A) b →
  Expr (system c u b) v → Vector A v → A
evaluate {c} {u} {b} {v} {A} cs us bs expr vs = recursor expr where
  recursor : Expr (system c u b) v → A
  recursor (var i) = vs i
  recursor (constant i) = cs i
  recursor (unary i x) = us i (recursor x)
  recursor (binary i x y) = bs i (recursor x) (recursor y)

{-
 - holes
 -}

data Hole (sys : System) (vars : ℕ) : Set where
  id : Hole sys vars
  unary : Fin (System.unary_num sys) → Hole sys vars → Hole sys vars
  binary-l : Fin (System.binary_num sys) → Expr sys vars → Hole sys vars → Hole sys vars
  binary-r : Fin (System.binary_num sys) → Hole sys vars → Expr sys vars → Hole sys vars

fill : ∀ {sys vars} → Hole sys vars → Expr sys vars → Expr sys vars
fill id x = x
fill (unary i xs) x = unary i (fill xs x)
fill (binary-l i x ys) y = binary i x (fill ys y)
fill (binary-r i xs y) x = binary i (fill xs x) y

_++_ : ∀ {sys vars} → Hole sys vars → Hole sys vars → Hole sys vars
id ++ ys = ys
unary i xs ++ ys = unary i (xs ++ ys)
binary-l i x ys₁ ++ ys = binary-l i x (ys₁ ++ ys)
binary-r i xs y ++ ys = binary-r i (xs ++ ys) y

module Properties where
  open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

  compose-var : ∀ {sys vars} x → compose {sys} {vars} {vars} x var ≡ x
  compose-var (var i) = refl
  compose-var (constant i) = refl
  compose-var (unary i x) =
    PropEq.cong (unary i) (compose-var x)
  compose-var (binary i x y) =
    PropEq.cong₂ (binary i) (compose-var x) (compose-var y)

  concat-fill : ∀ {sys vars} (xs ys : Hole sys vars) (z : Expr sys vars) →
    fill (xs ++ ys) z ≡ fill xs (fill ys z)
  concat-fill id ys z = refl
  concat-fill (unary i xs) ys z =
    PropEq.cong (unary i) (concat-fill xs ys z)
  concat-fill (binary-l i x ys₁) ys z =
    PropEq.cong (λ y → binary i x y) (concat-fill ys₁ ys z)
  concat-fill (binary-r i xs y) ys z =
    PropEq.cong (λ x → binary i x y) (concat-fill xs ys z)

