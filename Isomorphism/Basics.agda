module Basics where

Type : Set₁
Type = Set

Kind : Set₂
Kind = Set₁

id : ∀ {A : Type} → A → A
id x = x

data _≡_ {l} {A : Set l} (x : A) : A → Set₀ where
  refl : x ≡ x

J : ∀ {l₁} {l₂} {A : Set l₁} (x : A) → (M : (y : A) → x ≡ y → Set l₂)
  → (M x refl) → (y : A) → (p : x ≡ y) → M y p
J x M m _ refl = m

cong : ∀ {l₁} {l₂} {A : Set l₁} {B : Set l₂} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong {x = x} f = J x (λ y p → f x ≡ f y) refl _

trans : ∀ {l} {A : Set l} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans xeqy refl = xeqy

sym : ∀ {l} {A : Set l} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

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

