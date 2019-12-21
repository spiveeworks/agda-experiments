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
  a = var {magma} {3} Fin.zero
  b = var {magma} {3} (Fin.suc Fin.zero)
  c = var {magma} {3} (Fin.suc (Fin.suc Fin.zero))

_≈_ : ∀ {n} → ExprRel magma n
_≈_ {n} = Derivation {magma} {1} (assoc-raw ∷ []) n

assoc : ∀ {n} (x y z : Expr magma n) → ((x • y) • z) ≈ (x • (y • z))
assoc x y z = law Fin.zero (x ∷ y ∷ z ∷ [])

buildHole : ∀ {n} → List (Expr magma n) → Hole magma n
buildHole List.[] = id
buildHole (x List.∷ xs) = binary-r Fin.zero (buildHole xs) x

data Unzipped {n} : Expr magma n → Set where
  unzipped : ∀ i ys → Unzipped (fill (buildHole ys) (var i))

cons-unzipped : ∀ {n} x y → Unzipped {n} x → Unzipped {n} (x • y)
cons-unzipped .(_) y (unzipped i ys) = unzipped i (y List.∷ ys)

unzip : ∀ {n} x → Unzipped {n} x
unzip (var i) = unzipped i List.[]
unzip (binary Fin.zero x y) = cons-unzipped x y (unzip x)

data HeadNormal {n} (x : Expr magma n) : Set where
  varheadnormal : ∀ i → x ≈ var i → HeadNormal x
  opheadnormal : ∀ i y → x ≈ (var i • y) → HeadNormal x

cons-headnormal : ∀ {n} x z → HeadNormal {n} x → HeadNormal {n} (x • z)
cons-headnormal x z (varheadnormal i p) = opheadnormal i z p′ where
  p′ : (x • z) ≈ (var i • z)
  p′ = cong (binary-r Fin.zero id z) p
cons-headnormal x z (opheadnormal i y p) = opheadnormal i (y • z) p′ where
  p′ : (x • z) ≈ (var i • (y • z))
  p′ = trans (cong (binary-r Fin.zero id z) p) (assoc (var i) y z)

headnormalize : ∀ {n} x → HeadNormal {n} x
headnormalize (var i) = varheadnormal i refl
headnormalize (binary Fin.zero x y) = cons-headnormal x y (headnormalize x)

reduce : ∀ {n} → Fin n → List (Fin n) → Expr magma n
reduce i List.[] = var i
reduce i (j List.∷ js) = var i • (reduce j js)

data Normal {n} (x : Expr magma n) : Set where
  normal : ∀ i is → x ≈ reduce i is → Normal x

cons-normal : ∀ {n} x i y → x ≈ (var i • y) → Normal {n} y → Normal {n} x
cons-normal x i y xiy (normal j js yjs) = normal i (j List.∷ js) xijs where
  xijs = trans xiy (cong (binary-l Fin.zero (var i) id) yjs)

{-# TERMINATING #-}
normalize : ∀ {n} x → Normal {n} x
normalize x with headnormalize x
normalize x | (varheadnormal i p) = normal i List.[] p
normalize x | (opheadnormal i y p) = cons-normal x i y p (normalize y)

