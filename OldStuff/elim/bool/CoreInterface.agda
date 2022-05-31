open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record BoolCore (Bool : Set) : Set₁ where
  field
    true : Bool
    false : Bool
    elim : ∀ {C : Bool → Set} → C true → C false → ∀ (x : Bool) → C x
    β₁ : ∀ {C : Bool → Set} (ct : C true) (cf : C false) →
      elim ct cf true ≡ ct
    β₂ : ∀ {C : Bool → Set} (ct : C true) (cf : C false) →
      elim ct cf false ≡ cf

module Core where
    open import Data.Bool
    instance
        boolCore : BoolCore Bool
        BoolCore.true boolCore = Bool.true
        BoolCore.false boolCore = Bool.false
        BoolCore.elim boolCore ct cf true = ct
        BoolCore.elim boolCore ct cf false = cf
        BoolCore.β₁ boolCore _ _ = refl
        BoolCore.β₂ boolCore _ _ = refl
