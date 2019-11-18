module Reflection.Polynomial where

open import Reflection.Expr

open import Data.List as List using (List)
open import Data.Bool as Bool using (Bool)
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec using (Vec; _∷_; [])

ring : System
ring = system 4 (Vec.lookup (0 ∷ 0 ∷ 2 ∷ 2 ∷ []))

zeroOp : {A : Set} → Operator ring A
zeroOp = buildOp Fin.zero []

oneOp : {A : Set} → Operator ring A
oneOp = buildOp (Fin.suc Fin.zero) []

sumOp : {A : Set} → A → A → Operator ring A
sumOp x y =
  buildOp (Fin.suc (Fin.suc Fin.zero)) (x ∷ y ∷ [])

prodOp : {A : Set} → A → A → Operator ring A
prodOp x y =
  buildOp (Fin.suc (Fin.suc (Fin.suc Fin.zero))) (x ∷ y ∷ [])

freeRing : ℕ → System
freeRing = extend ring

{-
record Mondoid (M : Set) : Set where
  field
    m₀ : M
    _++_ : M → M → M

open Monoid {{...}} public
-}

-- without negation I guess this is a Rig
-- but the intended use cases is Bools which have negation
record Ring (R : Set) : Set where
  infixl 6 _+_
  infixl 7 _*_
  field
    r₀ : R
    r₁ : R
    _+_ : R → R → R
    _*_ : R → R → R

open Ring {{...}} public

instance
  freeRingRing : ∀ {n} → Ring (Expr (freeRing n))
  freeRingRing .r₀ = fromOp (injectOp zeroOp)
  freeRingRing .r₁ = fromOp (injectOp oneOp)
  freeRingRing ._+_ x y = fromOp (injectOp ( sumOp x y))
  freeRingRing ._*_ x y = fromOp (injectOp (prodOp x y))


{-
Polynomial : (R I : Set) (vars : ℕ) → Se
Polynomial R I n = (Fin n → I) → R

monomialEq : {A : Set} {{A → A → Bool}} {n : ℕ} →
  (Fin n → A) → (Fin n → A) → Bool
monomialEq {{_==_}} x y = foldr Bool._∧_ Bool.true (zipWith _==_ x y)

instance
  polyRing : ∀ {R I} {n} →
    {{Ring R}} → {{Monoid I}} → {{_==_ : I → I → Bool}} →
    Ring (Polynomial R I n)
  polyRing .r₀ is = r₀
  polyRing .r₁ is = Bool.if monomialEq is (λ _ → m₀) then r₁ else r₀
  polyRing ._+_ x y is = x is + y is
  polyRing ._*_ x y is = ?
-}

ringBaseSubst : ∀ {R} → {{_ : Ring R}} → Substitution ring R
ringBaseSubst Fin.zero [] = r₀
ringBaseSubst (Fin.suc Fin.zero) [] = r₁
ringBaseSubst (Fin.suc (Fin.suc Fin.zero)) (x ∷ y ∷ []) = x + y
ringBaseSubst (Fin.suc (Fin.suc (Fin.suc Fin.zero))) (x ∷ y ∷ []) = x * y

ringSubst : ∀ {R} {n} → {{_ : Ring R}} → (Fin n → R) → Substitution (freeRing n) R
ringSubst = extendSubst ring ringBaseSubst

