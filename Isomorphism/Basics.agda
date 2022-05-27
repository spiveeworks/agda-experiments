module Basics where

Type : Set₁
Type = Set

Kind : Set₂
Kind = Set₁

---------------------------
-- Polymoprhic Functions --
---------------------------

id : ∀ {l} {A : Set l} → A → A
id x = x

infixr 9 _∘_

_∘_ : ∀ {l₁} {l₂} {l₃} → {A : Set l₁} {B : Set l₂} {C : Set l₃}
  → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

--------------
-- Equality --
--------------

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

------------------------
-- Pointwise Equality --
------------------------

infix 4 _≈_

_≈_ : ∀ {l₁} {l₂} {A : Set l₁} {B : A → Set l₂}
  → ((x : A) → B x) → ((x : A) → B x) → Set l₁
f₁ ≈ f₂ = ∀ x → f₁ x ≡ f₂ x

fsym : ∀ {l₁} {l₂} {A : Set l₁} {B : Set l₂} → {f g : A → B} → f ≈ g → g ≈ f
fsym p x = sym (p x)

fsubst : ∀ {l₁} {l₂} {A : Set l₁} {B : Set l₂}
  → (f g : A → B) → f ≈ g →
  ∀ {x₁} {x₂} → f x₁ ≡ f x₂ → g x₁ ≡ g x₂
fsubst f g pw {x₁} {x₂} pf = trans (trans (sym (pw x₁)) pf) (pw x₂)

fsubst′ : ∀ {l₁} {l₂} {A : Set l₁} {B : Set l₂}
  → (f g : A → B) → f ≈ g →
  ∀ {x₁} {x₂} → f x₁ ≡ f x₂ → g x₁ ≡ g x₂
fsubst′ f g pw {x₁} {x₂} pf = trans (sym (pw x₁)) (trans pf (pw x₂))

IsBoolean : ∀ {l} {A : Set l} → (A → A) → Set l
IsBoolean f = f ∘ f ≈ f

IsInjective : ∀ {l₁} {l₂} {A : Set l₁} {B : Set l₂}
  → (A → B) → Set l₁
IsInjective f = ∀ x₁ x₂ → f x₁ ≡ f x₂ → x₁ ≡ x₂

id-is-boolean : ∀ {l} {A : Set l}
  → (f : A → A) → f ≈ id → IsBoolean f
id-is-boolean f p x = cong f (p x)

id-is-injective : ∀ {l} {A : Set l}
  → (f : A → A) → f ≈ id → IsInjective f
id-is-injective f pw _ _ pf = fsubst f id pw pf

id-is-injective′ : ∀ {l} {A : Set l}
  → (f : A → A) → f ≈ id → IsInjective f
id-is-injective′ f pw _ _ pf = fsubst′ f id pw pf

injective-boolean : ∀ {l} {A : Set l}
  → (f : A → A) → IsInjective f → IsBoolean f → f ≈ id
injective-boolean f inj bool x = inj (f x) x (bool x)

--------------
-- Inverses --
--------------

record _↔_ (A B : Type) : Type where
  field
    fwd : A → B
    bwd : B → A
    right : fwd ∘ bwd ≈ id
    left : bwd ∘ fwd ≈ id

refl-bij : ∀ A → A ↔ A
refl-bij A = record {fwd = id; bwd = id; left = λ x → refl; right = λ y → refl}

inv-bij : ∀ {A} {B} → A ↔ B → B ↔ A
inv-bij record{fwd = fwd; bwd = bwd; left = left; right = right} =
  record{fwd = bwd; bwd = fwd; left = right; right = left}

-----------------
-- Isomorphism --
-----------------

semi-from-right : {A B : Type} → (f : A → B) → (g : B → A)
  → f ∘ g ≈ id → g ∘ f ∘ g ≈ g
semi-from-right f g ri y = cong g (ri y)

semi-from-left : {A B : Type} → (f : A → B) → (g : B → A)
  → g ∘ f ≈ id → g ∘ f ∘ g ≈ g
semi-from-left f g li y = li (g y)

InvProofsCommute : {A B : Type} → (f : A → B) → (g : B → A)
  → g ∘ f ≈ id → f ∘ g ≈ id → Type
InvProofsCommute f g left right =
  semi-from-left f g left ≈ semi-from-right f g right

record _≅_ (A B : Type) : Type where
  field
    fwd : A → B
    bwd : B → A
    left : bwd ∘ fwd ≈ id
    right : fwd ∘ bwd ≈ id
    commute : InvProofsCommute bwd fwd right left  -- Excuse the reversal.

refl-iso : ∀ A → A ≅ A
refl-iso A = record {fwd = id; bwd = id; left = λ x → refl; right = λ y → refl; commute = λ x → refl}

