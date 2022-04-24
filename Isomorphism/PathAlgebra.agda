Type : Set₁
Type = Set

Kind : Set₂
Kind = Set₁

id : ∀ {A : Type} → A → A
id x = x

infix 4 _≡_

data _≡_ {A : Type} (x : A) : A → Set where
  refl : x ≡ x

infixr 6 _$_
infixr 5 _++_ -_ _+-_

_++_ : ∀ {A} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
xeqy ++ refl = xeqy

_$_ : ∀ {A} {B} → {x y  : A} → (f : A → B) → x ≡ y → f x ≡ f y
f $ refl = refl

-_ : ∀ {A} → {x y : A} → x ≡ y → y ≡ x
- refl = refl

_+-_ : ∀ {A} → {x y z : A} → x ≡ y → z ≡ y → x ≡ z
p₁ +- p₂ = p₁ ++ (- p₂)

dist : ∀ {A} {B} {x y z : A} (f : A → B) (p₁ : x ≡ y) (p₂ : y ≡ z)
  → f $ (p₁ ++ p₂) ≡ f $ p₁ ++ f $ p₂
dist f p₁ refl = refl

assoc : ∀ {A} {w x y z : A} (p₁ : w ≡ x) (p₂ : x ≡ y) (p₃ : y ≡ z)
  → (p₁ ++ p₂) ++ p₃ ≡ p₁ ++ p₂ ++ p₃
assoc p₁ p₂ refl = refl

inv : ∀ {A} {x y : A} (p : x ≡ y) → p +- p ≡ refl
inv refl = refl

left-ident : ∀ {A} {x y : A} (p : x ≡ y) → refl ++ p ≡ p
left-ident refl = refl

neg-dist : ∀ {A} {x y z : A} (p₁ : x ≡ y) (p₂ : y ≡ z)
  →  (- p₂) ++ (- p₁) ≡ - (p₁ ++ p₂)
neg-dist p₁ refl = left-ident (- p₁)


