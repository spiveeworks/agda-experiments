module Basics where

Type : Set₁
Type = Set

Kind : Set₂
Kind = Set₁

id : ∀ {A : Type} → A → A
id x = x

infix 4 _≡_

data _≡_ {l} {A : Set l} (x : A) : A → Set₀ where
  refl : x ≡ x

J : ∀ {l₁} {l₂} {A : Set l₁} (x : A) → (M : (y : A) → x ≡ y → Set l₂)
  → (M x refl) → (y : A) → (p : x ≡ y) → M y p
J x M m _ refl = m

transp : ∀ {l₁} {l₂} {A : Set l₁} (F : (x : A) → Set l₂)
  → {x₁ x₂ : A} → x₁ ≡ x₂ → F x₁ → F x₂
transp F {x₁} {x₂} p m = J x₁ (λ x _ → F x) m x₂ p

cong : ∀ {l₁} {l₂} {A : Set l₁} {B : Set l₂} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong {x = x} f p = transp (λ y → f x ≡ f y) p refl

trans : ∀ {l} {A : Set l} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans xeqy refl = xeqy

sym : ∀ {l} {A : Set l} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

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

conj-cancel-l : ∀ {l} {A : Set l} (f : A → A) (tr : ∀ x → f x ≡ x)
  → ∀ {x} {y} → (p : x ≡ y)
  → trans (trans (sym (tr x)) (cong f p)) (tr y) ≡ p
conj-cancel-l f tr {x} refl = sym-inv-l (tr x)

conj-cancel-r : ∀ {l} {A : Set l} (f : A → A) (tr : ∀ x → f x ≡ x)
  → ∀ {x} {y} → (p : x ≡ y)
  → trans (sym (tr x)) (trans (cong f p) (tr y)) ≡ p
conj-cancel-r f tr {x} refl = trans
  (cong (trans (sym (tr x))) (trans-id-l (tr x))) -- trans refl (tr x) ≡ tr x
  (sym-inv-l (tr x)) -- trans (sym (tr x)) (tr x) ≡ refl

conj-contract-r : ∀ {l} {A : Set l} (f : A → A) (tr : ∀ x → f x ≡ x)
  → ∀ {x} {y} → (p : x ≡ y)
  → trans (tr x) (trans p (sym (tr y))) ≡ cong f p
conj-contract-r f tr {x} refl = trans
  (cong (trans (tr x)) (trans-id-l (sym (tr x)))) -- trans refl (sym (tr x)) ≡ sym (tr x)
  (sym-inv-r (tr x)) -- trans (tr x) (sym (tr x)) ≡ refl

record _≅_ (A B : Type) : Type where
  field
    fwd : A → B
    bwd : B → A
    fwdbwd : ∀ x → bwd (fwd x) ≡ x
    bwdfwd : ∀ y → fwd (bwd y) ≡ y

refl-iso : ∀ A → A ≅ A
refl-iso A = record {fwd = id; bwd = id; fwdbwd = λ x → refl; bwdfwd = λ y → refl}

inv-iso : ∀ {A} {B} → A ≅ B → B ≅ A
inv-iso record{fwd = fwd; bwd = bwd; fwdbwd = fwdbwd; bwdfwd = bwdfwd} = record{fwd = bwd; bwd = fwd; fwdbwd = bwdfwd; bwdfwd = fwdbwd}

IsRightInv : {A B : Type} → (f : A → B) → (g : B → A) → Type
IsRightInv f g = ∀ y → f (g y) ≡ y

right-inv-commute : {A B : Type} → (f : A → B) → (g : B → A)
  → ∀ (fog : IsRightInv f g)
  → ∀ y → cong (λ y → f (g y)) (fog y) ≡ fog (f (g y))
right-inv-commute f g fog y = trans
  (sym (conj-contract-r (λ y → f (g y)) fog (fog y)))
  (cong (trans (fog (f (g y)))) (sym-inv-r (fog y)))

right-inv-commute′ : {A B : Type} → (f : A → B) → (g : B → A)
  → ∀ (fog : IsRightInv f g)
  → ∀ y → cong f (cong g (fog y)) ≡ fog (f (g y))
right-inv-commute′ f g fog y = trans
  (cong-commute f g (fog y))
  (right-inv-commute f g fog y)

right-inv-fgf-commute : {A B : Type} → (f : A → B) → (g : B → A)
  → ∀ (fog : IsRightInv f g)
  → ∀ y → cong (λ x → g (f x)) (cong g (fog y)) ≡ cong g (fog (f (g y)))
right-inv-fgf-commute f g fog y = trans
  (sym (cong-commute g f (cong g (fog y))))
  (cong (cong g) (right-inv-commute′ f g fog y))

IsNatural : {A B : Type} → (iso : A ≅ B) → Type
IsNatural record{fwd = f; bwd = g; fwdbwd = gof; bwdfwd = fog}
  = ∀ x → fog (f x) ≡ cong f (gof x)

natbwdfwd : {A B : Type} → (iso : A ≅ B) → ∀ y → _≅_.fwd iso (_≅_.bwd iso y) ≡ y
natbwdfwd record{fwd = f; bwd = g; fwdbwd = gof; bwdfwd = fog} y
  = trans (trans (sym (fog (f (g y)))) (cong f (gof (g y)))) (fog y)

mknatiso : {A B : Type} → A ≅ B → A ≅ B
mknatiso iso = record{
  fwd = _≅_.fwd iso;
  bwd = _≅_.bwd iso;
  fwdbwd = _≅_.fwdbwd iso;
  bwdfwd = natbwdfwd iso}

nat-proof-raw : ∀ {A B : Type} → (iso : A ≅ B)
  → ∀ x → natbwdfwd iso (_≅_.fwd iso x) ≡ cong (_≅_.fwd iso) (_≅_.fwdbwd iso x)
nat-proof-raw record{fwd = f; bwd = g; fwdbwd = gof; bwdfwd = fog} x = trans
  (cong
    (λ p → trans (trans (sym (fog (f (g (f x))))) p) (fog (f x)))
    (sym (right-inv-fgf-commute g f gof x)))
  (conj-cancel-l (λ y → f (g y)) fog (cong f (gof x)))

nat-proof : ∀ {A B : Type} → (iso : A ≅ B) → IsNatural (mknatiso iso)
nat-proof = nat-proof-raw

