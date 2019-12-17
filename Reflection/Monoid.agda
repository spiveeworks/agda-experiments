module Reflection.Monoid where

open import Reflection.Expr
open import Reflection.Equation

open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.List as List using (List)
open import Data.Vec as Vec using (Vec; _∷_; [])

monoid : System
monoid = system 2 (Vec.lookup (0 ∷ 2 ∷ []))

zeroOp : {A : Set} → Operator monoid A
zeroOp = buildOp Fin.zero []

sumOp : {A : Set} → A → A → Operator monoid A
sumOp x y = buildOp (Fin.suc Fin.zero) (x ∷ y ∷ [])

freeMonoid : ℕ → System
freeMonoid = extend monoid

record Monoid (M : Set) : Set where
  infixl 6 _++_
  field
    m₀ : M
    _++_ : M → M → M

open Monoid {{...}} public

instance
  freeMonoidMonoid : ∀ {n} → Monoid (Expr (freeMonoid n))
  freeMonoidMonoid .m₀ = fromOp (injectOp zeroOp)
  freeMonoidMonoid ._++_ x y = fromOp (injectOp (sumOp x y))

{-
  functionMonoid : ∀ {n} → Monoid (Expr (extend (freeMonoid n) 1))
  functionMonoid .m₀ = fromOp (injectOp (injectOp zeroOp))
  functionMonoid ._++_ x y = fromOp (injectOp (injectOp (sumOp x y)))
  -}

monoidLaws = Vec.lookup (
  ((m₀ ++ a₁) :≈ a₁) ∷
  ((a₁ ++ m₀) :≈ a₁) ∷
  (((a₃ ++ b₃) ++ c₃) :≈ (a₃ ++ (b₃ ++ c₃))) ∷
  []) where
  a₁ = var {monoid} {1} Fin.zero
  a₃ = var {monoid} {3} Fin.zero
  b₃ = var {monoid} {3} (Fin.suc Fin.zero)
  c₃ = var {monoid} {3} (Fin.suc (Fin.suc Fin.zero))

_≈_ : {m : ℕ} → Eq (freeMonoid m)
_≈_ {m} = Derivation monoidLaws m

{-
left-identity : ∀ {m} x → _≈_ {m} (m₀ ++ x) x
left-identity x = inject (raw
  Fin.zero
  (intro (var Fin.zero) (λ _ → x)))

right-identity : ∀ {m} x → _≈_ {m} (x ++ m₀) x
right-identity x = inject (raw
  (Fin.suc Fin.zero)
  (intro (var Fin.zero) (λ _ → x)))

associativity : ∀ {m} x y z → _≈_ {m} ((x ++ y) ++ z) (x ++ (y ++ z))
associativity x y z = inject (raw
  (Fin.suc (Fin.suc Fin.zero))
  (intro (var Fin.zero) (Vec.lookup (x ∷ y ∷ z ∷ []))))
-}

data HeadNormal (m : ℕ) (x : Expr (freeMonoid m)) : Set where
  zero : x ≈ m₀ → HeadNormal m x
  one : (i : Fin m) → x ≈ var i → HeadNormal m x
  cons : (i : Fin m) → (y : Expr (freeMonoid m)) →
    x ≈ (var i ++ y) → HeadNormal m x

composeHead : ∀ {m} x y → x ≈ y → HeadNormal m y → HeadNormal m x
composeHead {m} x y p hy = ?

associateHead : ∀ {m} x y → HeadNormal m x → HeadNormal m y → HeadNormal m (x ++ y)
associateHead x y hx hy = ?

getHead : ∀ {m} x → HeadNormal m x
getHead (fromOp (buildOp Fin.zero [])) = zero refl
getHead (fromOp (buildOp (Fin.suc (Fin.suc i)) [])) = one i refl
getHead (fromOp (buildOp (Fin.suc Fin.zero) (x ∷ y ∷ []))) = ?

