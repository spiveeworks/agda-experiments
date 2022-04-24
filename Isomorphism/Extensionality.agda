module Extensionality where

open import Basics

postulate
  ext : ∀ {l₁} {l₂} {A : Set l₁} {B : A → Set l₂} (f g : (x : A) → B x)
    → ((x : A) → f x ≡ g x) → f ≡ g

postulate
  ext-elim-J : ∀ {l₁} {l₂} {l₃} {A : Set l₁} {B : A → Set l₂}
    (f g : (x : A) → B x) → (pw : (x : A) → f x ≡ g x)
    → (x : A) → (M : (y : B x) → Set l₃)
    → (m : M (f x))
    → J f (λ f₀ _ → M (f₀ x)) m g (ext f g pw)
    ≡ J (f x) (λ y _ → M y) m (g x) (pw x)

ext-elim-cong : ∀ {l₁} {l₂} {A : Set l₁} {B : A → Set l₂} {C : Set}
  (f g : (x : A) → B x) → (pw : (x : A) → f x ≡ g x) → (x : A) → (h : B x → C)
  → cong (λ f₀ → h (f₀ x)) (ext f g pw) ≡ cong h (pw x)
ext-elim-cong f g pw x h = ext-elim-J f g pw x _ _


