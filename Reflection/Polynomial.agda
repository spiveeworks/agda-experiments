module Reflection.Polynomial where

open import Reflection.Expr

open import Data.List as List using (List)
open import Data.Bool as Bool using (Bool)
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.Vec.Functional as Vector using (Vector; _∷_; [])

ring = system 2 0 2

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
  freeRing : ∀ {n} → Ring (Expr ring n)
  freeRing .r₀ = constant Fin.zero
  freeRing .r₁ = constant (Fin.suc Fin.zero)
  freeRing ._+_ = binary Fin.zero
  freeRing ._*_ = binary (Fin.suc Fin.zero)

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

ringEval : ∀ {R n} → {{_ : Ring R}} → Expr ring n → Vector R n → R
ringEval = evaluate (r₀ ∷ r₁ ∷ []) [] (_+_ ∷ _*_ ∷ [])

