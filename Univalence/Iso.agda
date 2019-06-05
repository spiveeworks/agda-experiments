{-# OPTIONS --cubical #-}
open import Agda.Primitive
open import Cubical.Core.Everything

refl : ∀ {a} {A : Set a} {x : A} → x ≡ x
refl {x = x} i = x

IsContr : ∀ {a} (A : Set a) → Set a
IsContr A = Σ A λ x₁ → ∀ x₂ → x₁ ≡ x₂

Fiber : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (y : B) → Set (a ⊔ b)
Fiber f y = Σ _ λ x → f x ≡ y

_IsLeftInverseOf_ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (g : B → A) → Set b
f IsLeftInverseOf g = ∀ y → f (g y) ≡ y

IsInjective : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → Set (a ⊔ b)
IsInjective f = ∀ x₁ x₂ → f x₁ ≡ f x₂ → x₁ ≡ x₂

inj-proof : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (g : B → A) →
  g IsLeftInverseOf f → IsInjective f
inj-proof f g inv x₁ x₂ p i = hcomp
  (λ h → λ {(i = i0) → inv x₁ h;(i = i1) → inv x₂ h})
  (g (p i))

record _↔_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    fwd : A → B
    bwd : B → A
    surj : fwd IsLeftInverseOf bwd
    inj : bwd IsLeftInverseOf fwd

open _↔_

fromEquiv : ∀ {a b} {A : Set a} {B : Set b} → A ≃ B → A ↔ B
fromEquiv {A = A} {B = B} e = iso where
  map = e .fst
  equiv = e .snd .equiv-proof
  iso : A ↔ B
  iso .fwd = map
  iso .bwd y = equiv y .fst .fst
  iso .surj y = equiv y .fst .snd
  iso .inj x i = equiv (map x) .snd (x , λ j → map x) i .fst

contractInj : ∀ {a b} {A : Set a} {B : Set b} → (f : A → B) → IsInjective f →
  ∀ (x : A) → IsContr (Fiber f (f x))
contractInj f inj x₁ = (x₁ , refl) , contract where
  contract : ∀ z → (x₁ , refl) ≡ z
  contract (x₂ , fp) i = ? where --p (~ i) , λ j → f (p (~ i ∧ j)) where
    p : x₂ ≡ x₁
    p = inj x₂ x₁ fp


{-
fromIso : ∀ {a b} {A : Set a} {B : Set b} → A ↔ B → A ≃ B
fromIso {A = A} {B = B} iso = iso .fwd , eq where
  eq : isEquiv (iso .fwd)
  eq .equiv-proof y = centre , contract where
    centre = iso .bwd y , iso .surj y
    contract : ∀ (z : Σ A λ x → iso .fwd x ≡ y) → centre ≡ z
    contract z = ?
-}
