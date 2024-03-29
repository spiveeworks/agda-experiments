open import Basics
open _≅_

open import HigherEquality

record Fiber {l} {A B : Set l} (f : A → B) (y : B) : Set l where
  constructor fiber
  field
    preimage : A
    path : f preimage ≡ y

fiber-path : ∀ {l} {A B : Set l} {f : A → B} {y : B} {x₁ x₂ : A}
  {p₁ : f x₁ ≡ y} {p₂ : f x₂ ≡ y}
  (px : x₁ ≡ x₂) (q : transp (λ x → f x ≡ y) px p₁ ≡ p₂)
  → fiber x₁ p₁ ≡ fiber x₂ p₂
fiber-path refl refl = refl

record IsContr {l} (A : Set l) : Set l where
  field
    centre : A
    path-from : ∀ x → x ≡ centre

IsWEquiv : ∀ {l} {A B : Set l} (f : A → B) → Set l
IsWEquiv f = ∀ y → IsContr (Fiber f y)

record WEquiv {l} (A B : Set l) : Set l where
  field
    f : A → B
    is-wequiv : IsWEquiv f

iso-fiber : {A B : Type} → (iso : A ≅ B) → ∀ y → Fiber (fwd iso) y
iso-fiber iso y = fiber (bwd iso y) (right iso y)

helper : ∀ {A B : Type} (f : A → B) {x₁ x₂ : A}
  (p₁ : x₂ ≡ x₁) (p₂ : f x₂ ≡ f x₁)
  → (cong f p₁ ≡ p₂) → transp (λ x → f x ≡ f x₁) (sym p₁) refl ≡ p₂
helper f refl p₂ q = q

iso-fiber-is-centre : {A B : Type} → (iso : A ≅ B)
  → ∀ y → ∀ (pre : Fiber (fwd iso) y) → pre ≡ iso-fiber iso y
iso-fiber-is-centre iso _ (fiber x refl) = fiber-path
  (sym (left iso x))
  (helper (fwd iso) (left iso x) (right iso (fwd iso x)) (sym (commute iso x)))

WEquiv-from-iso : (A B : Type) → (iso : A ≅ B) → WEquiv A B
WEquiv-from-iso A B iso = record{
  f = fwd iso;
  is-wequiv = λ y → record{
    centre = iso-fiber iso y;
    path-from = iso-fiber-is-centre iso y}}

WEquiv-from-bij : (A B : Type) → (iso : A ↔ B) → WEquiv A B
WEquiv-from-bij A B bij = WEquiv-from-iso A B (mk-iso bij)
