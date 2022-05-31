open import Relation.Binary
open import Algebra using (Semigroup)
import Algebra.FunctionProperties

module Analysis.Completion
  {a l} (S : Semigroup a l)
  (comm : Algebra.FunctionProperties.Commutative (Semigroup._≈_ S) (Semigroup._∙_ S)) where

module Base = Semigroup S
C : Set a
C = Base.Carrier

record Carrier : Set a where
  constructor _:-_
  field
    pos : C
    neg : C

_∙_ : Carrier → Carrier → Carrier
(x₁ :- y₁) ∙ (x₂ :- y₂) = (x₁ Base.∙ x₂) :- (y₁ Base.∙ y₂)

_⁻¹ : Carrier → Carrier
(x₁ :- y₁) ⁻¹ = y₁ :- x₁

IsIdent : Carrier → Set l
IsIdent (x₁ :- y₁) = x₁ Base.≈ y₁

_≈_ : Rel Carrier l
x ≈ y = IsIdent (x ∙ (y ⁻¹))

module Props = Algebra.FunctionProperties Base._≈_
module Props′ = Algebra.FunctionProperties _≈_

Δ : C → Carrier
Δ x₀ = x₀ :- x₀

fromPairwiseEq : ∀ {x₁ x₂ y₁ y₂} →
  x₁ Base.≈ x₂ → y₁ Base.≈ y₂ → (x₁ :- y₁) ≈ (x₂ :- y₂)
fromPairwiseEq eq₁ eq₂ = ?

left-ident : ∀ x → Props′.LeftIdentity (Δ x) _∙_
-- to clarify, goal evaluates to ((x₀ x₁) y₁) = ((x₀ y₁) x₁)
left-ident x₀ (x₁ :- y₁) = ?

assoc : Props.Associative Base._∙_ → Props′.Associative _∙_
assoc inner (x₁ :- y₁) (x₂ :- y₂) (x₃ :- y₃) = ?
