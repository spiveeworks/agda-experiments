module HigherEquality where

open import Basics

--------------------------------------
-- Properties of transp derivatives --
--------------------------------------

cong-commute : ∀ {l₁} {l₂} {l₃} {A : Set l₁} {B : Set l₂} {C : Set l₃}
  → {x y : A} → (f : B → C) → (g : A → B)
  → ∀ (p : x ≡ y) → cong f (cong g p) ≡ cong (λ z → f (g z)) p
cong-commute f g refl = refl

trans-id-l : ∀ {l} {A : Set l} → {x y : A} → (p : x ≡ y) → trans refl p ≡ p
trans-id-l refl = refl

sym-inv-r : ∀ {l} {A : Set l} → {x y : A} → ∀ (p : x ≡ y) → trans p (sym p) ≡ refl
sym-inv-r refl = refl

sym-inv-l : ∀ {l} {A : Set l} → {x y : A} → ∀ (p : x ≡ y) → trans (sym p) p ≡ refl
sym-inv-l refl = refl

sym-sym-elim : ∀ {l} {A : Set l} → {x y : A} → ∀ (p : x ≡ y) → sym (sym p) ≡ p
sym-sym-elim refl = refl

-----------------------
-- fsubst properties --
-----------------------

fsubst-refl : ∀ {l₁} {l₂} {A : Set l₁} {B : Set l₂}
  → (f g : A → B) → (pw : f ≈ g) → (x : A)
  → fsubst f g pw {x} {x} refl ≡ refl
fsubst-refl f g pw x = sym-inv-l (pw x)

fsubst′-refl : ∀ {l₁} {l₂} {A : Set l₁} {B : Set l₂}
  → (f g : A → B) → (pw : f ≈ g) → (x : A)
  → fsubst′ f g pw {x} {x} refl ≡ refl
fsubst′-refl f g pw x = trans
  (cong (trans (sym (pw x))) (trans-id-l (pw x))) -- trans refl (pw x) ≡ pw x
  (sym-inv-l (pw x)) -- trans (sym (pw x)) (pw x) ≡ refl

id-inj-cancel : ∀ {l} {A : Set l} (f : A → A) (tr : f ≈ id)
  → ∀ {x₁} {x₂} (p : x₁ ≡ x₂)
  → id-is-injective f tr x₁ x₂ (cong f p) ≡ p
id-inj-cancel f tr {x} refl = fsubst-refl f id tr x

id-inj′-cancel : ∀ {l} {A : Set l} (f : A → A) (tr : f ≈ id)
  → ∀ {x₁} {x₂} (p : x₁ ≡ x₂)
  → id-is-injective′ f tr x₁ x₂ (cong f p) ≡ p
id-inj′-cancel f tr {x} refl = fsubst′-refl f id tr x

-- fsubst can be used in place of cong for identity functions.
-- It will turn out to be equal to cong, meaning cong inherits some properties
-- of fsubst in all of the cases where fsubst could have been used instead.
fsubst′-cong : ∀ {l} {A : Set l} → (f : A → A) → (tr : f ≈ id)
  → ∀ {x₁ x₂ : A} → x₁ ≡ x₂ → f x₁ ≡ f x₂
fsubst′-cong f tr = fsubst′ id f (fsym tr)

fsubst′-cong-is-cong : ∀ {l} {A : Set l} → (f : A → A) → (tr : f ≈ id)
  → ∀ {x₁ x₂ : A} → (p : x₁ ≡ x₂) → fsubst′-cong f tr p ≡ cong f p
fsubst′-cong-is-cong f tr {x} refl = fsubst′-refl id f (fsym tr) x

-- fsubst′-cong simplifies to tr (f x), when p = tr x
fsubst′-cong-is-comp : ∀ {l} {A : Set l} → (f : A → A) → (tr : f ≈ id)
  → ∀ {x : A} → fsubst′-cong f tr (tr x) ≡ tr (f x)
fsubst′-cong-is-comp f tr {x} = trans
  (cong (trans _) (sym-inv-r (tr x)))
  (sym-sym-elim (tr (f x)))

id-cong-commute : {A : Type} → (f : A → A) → (tr : f ≈ id)
  → ∀ x → cong f (tr x) ≡ tr (f x)
id-cong-commute f tr x = trans
  (sym (fsubst′-cong-is-cong f tr (tr x)))
  (fsubst′-cong-is-comp f tr)

-- Special case when the identity function is a composition of inverses.
inv-cong-commute : {A B : Type} → (f : A → B) → (g : B → A)
  → ∀ (fog : f ∘ g ≈ id)
  → ∀ y → cong f (cong g (fog y)) ≡ fog (f (g y))
inv-cong-commute f g fog y = trans
  (cong-commute f g (fog y))
  (id-cong-commute (f ∘ g) fog y)

-------------------------------------------
-- Building Isomorphisms from Bijections --
-------------------------------------------

mk-iso-right : {A B : Type}
  → (bij : A ↔ B) → _↔_.fwd bij ∘ _↔_.bwd bij ≈ id
mk-iso-right record{fwd = f; bwd = g; left = gof; right = fog} y =
  id-is-injective (f ∘ g) fog _ _ (cong f (gof (g y)))

iso-right-proof : {A B : Type} → (bij : A ↔ B)
  → InvProofsCommute (_↔_.bwd bij) (_↔_.fwd bij) (mk-iso-right bij) (_↔_.left bij)
iso-right-proof record{fwd = f; bwd = g; left = gof; right = fog} x = trans
  (cong (id-is-injective (f ∘ g) fog _ _) fgf-commute)
  (id-inj-cancel (f ∘ g) fog (cong f (gof x)))
  where fgf-commute : cong f (gof (g (f x))) ≡ cong (f ∘ g) (cong f (gof x))
        fgf-commute = trans
          (sym (cong (cong f) (inv-cong-commute g f gof x)))
          (cong-commute f g (cong f (gof x)))

mk-iso : {A B : Type} → A ↔ B → A ≅ B
mk-iso bij = record{
  fwd = _↔_.fwd bij;
  bwd = _↔_.bwd bij;
  right = mk-iso-right bij;
  left = _↔_.left bij;
  commute = iso-right-proof bij}

