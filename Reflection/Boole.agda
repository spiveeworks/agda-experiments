module Reflection.Boole where

open import Reflection.Expr
open import Reflection.Polynomial

open import Data.Bool as Bool
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec using (Vec; _∷_; [])

instance
  boolRing : Ring Bool
  boolRing .r₀ = false
  boolRing .r₁ = true
  boolRing ._+_ = _xor_
  boolRing ._*_ = _∧_

data PolyBool : ℕ → Set where
  scalar : Bool → PolyBool 0
  _+x*_ : {n : ℕ} → PolyBool n → PolyBool n → PolyBool (ℕ.suc n)

fromBool : ∀ {n} → Bool → PolyBool n
fromBool {ℕ.zero} t = scalar t
fromBool {ℕ.suc _} t = fromBool t +x* fromBool false

zipWith : ∀ {n} → (Bool → Bool → Bool) → PolyBool n → PolyBool n → PolyBool n
zipWith f (scalar a) (scalar b) = scalar (f a b)
zipWith f (a₀ +x* a₁) (b₀ +x* b₁) =
  (zipWith f a₀ b₀) +x* (zipWith f a₁ b₁)

lookup : ∀ {n} → PolyBool n → Vec Bool n → Bool
lookup (scalar t) [] = t
lookup (a₀ +x* a₁) (false ∷ is) = lookup a₀ is
lookup (a₀ +x* a₁) (true ∷ is) = lookup a₁ is

instance
  polyBoolRing : ∀ {n} → Ring (PolyBool n)
  polyBoolRing .r₀ = fromBool r₀
  polyBoolRing .r₁ = fromBool r₁
  polyBoolRing ._+_ = zipWith _+_
  polyBoolRing ._*_ (scalar a) (scalar b) = scalar (a * b)
  polyBoolRing ._*_ (a₀ +x* a₁) (b₀ +x* b₁) =
    (a₀ * b₀) +x* (a₀ * b₁ + a₁ * b₀ + a₁ * b₁)

linearMonomial : ∀ {n} → Fin n → PolyBool n
linearMonomial Fin.zero = r₀ +x* r₁
linearMonomial (Fin.suc i) = (linearMonomial i) +x* r₀

polyBoolSubst : ∀ {n} → Substitution (freeRing n) (PolyBool n)
polyBoolSubst = ringSubst linearMonomial

simplify : ∀ {n} → Expr (freeRing n) → PolyBool n
simplify {n} = evaluate (freeRing n) polyBoolSubst

module tests where
  open import Relation.Binary.PropositionalEquality
  open import Reflection.Expr

  test-0 : simplify {2} r₀ ≡ r₀
  test-0 = refl

  test-1 : simplify {2} r₁ ≡ r₁
  test-1 = refl

  test-+ : simplify {2} (var {ring} Fin.zero + var {ring} (Fin.suc Fin.zero)) ≡
    ((scalar false) +x* (scalar true)) +x* ((scalar true) +x* (scalar false))
  test-+ = refl
  test-* : simplify {2} (var {ring} Fin.zero * var {ring} (Fin.suc Fin.zero)) ≡
    ((scalar false) +x* (scalar false)) +x* ((scalar false) +x* (scalar true))
  test-* = refl

  _⟨+⟩_ : ∀ {R} {{_ : Ring R}} → R → R → R
  x ⟨+⟩ y = x + y + x * y

  test-⟨+⟩ : simplify {2} (var {ring} Fin.zero ⟨+⟩ var {ring} (Fin.suc Fin.zero)) ≡
    ((scalar false) +x* (scalar true)) +x* ((scalar true) +x* (scalar true))
  test-⟨+⟩ = refl

