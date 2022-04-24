open import Basics
open _≅_

record Fiber {l} {A B : Set l} (f : A → B) (y : B) : Set l where
  field
    preimage : A
    path : f preimage ≡ y

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
iso-fiber iso y = record{preimage = bwd iso y; path = bwdfwd iso y}

iso-fiber-is-centre : {A B : Type} → (iso : A ≅ B) → ∀ y →
  ∀ (pre : Fiber (fwd iso) y) → pre ≡ iso-fiber iso y
iso-fiber-is-centre iso y pre = ?

WEquiv-from-iso : (A B : Type) → A ≅ B → WEquiv A B
WEquiv-from-iso A B iso = record{
  f = fwd iso;
  is-wequiv = λ y → record{
    centre = iso-fiber iso y;
    path-from = iso-fiber-is-centre iso y}}
