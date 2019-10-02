{-# OPTIONS --without-K #-}

_≡_ : ∀ {l} {A : Set l} → A → A → Set _
_≡_ {A = A} x y = ∀ (C : A → A → Set) → (∀ x → C x x) → C x y

refl : ∀ {l} {A : Set l} {x : A} → x ≡ x
refl {x = x} C z = z x

Interval : Set₁
Interval = ∀ (A : Set) → (x y : A) → x ≡ y → A

i1 : Interval
i1 A x y p = x

i2 : Interval
i2 A x y p = y

postulate ext : ∀ {l₁} {l₂} → {A : Set l₁} → {B : A → Set l₂} → (f g : (x : A) → B x) → (∀ x → f x ≡ g x) → f ≡ g

ipath : i1 ≡ i2
ipath = ext _ _ (λ A →
  ext _ _ (λ x →
  ext _ _ (λ y →
  ext _ _ (λ p → p))))


S¹ : Set₁
S¹ = ∀ (A : Set) → (x : A) → x ≡ x → A

base : S¹
base A x p = x

loop : base ≡ base
loop = ext _ _ (λ A →
  ext _ _ (λ x →
  ext _ _ (λ p → p)))


-- this isn't actually a torus though? I'm very new to homotopies
Torus : Set₁
Torus = ∀ (A : Set) → (x : A) → (p₁ p₂ : x ≡ x) → p₁ ≡ p₂ → A

point : Torus
point A x p₁ p₂ sq = x

line₁ : point ≡ point
line₁ = ext _ _ (λ A →
  ext _ _ (λ x →
  ext _ _ (λ p₁ →
  ext _ _ (λ p₂ →
  ext _ _ (λ sq → p₁)))))

line₂ : point ≡ point
line₂ = ext _ _ (λ A →
  ext _ _ (λ x →
  ext _ _ (λ p₁ →
  ext _ _ (λ p₂ →
  ext _ _ (λ sq → p₂)))))

line₁pw : ∀ A x p₁ p₂ sq → point A x p₁ p₂ sq ≡ point A x p₁ p₂ sq
line₁pw A x p₁ p₂ sq = p₁

line₂pw : ∀ A x p₁ p₂ sq → point A x p₁ p₂ sq ≡ point A x p₁ p₂ sq
line₂pw A x p₁ p₂ sq = p₂

squarehelper : line₁pw ≡ line₂pw
squarehelper = ext _ _ (λ A →
  ext _ _ (λ x →
  ext _ _ (λ p₁ →
  ext _ _ (λ p₂ →
  ext _ _ (λ sq → sq)))))

square : line₁ ≡ line₂
square C z = squarehelper
  (λ f₁ f₂ → C
    (ext _ _ (λ A → ext _ _ (λ x → ext _ _ (λ p₁ → ext _ _ (λ p₂ → ext _ _
      (λ sq → f₁ A x p₁ p₂ sq))))))
    (ext _ _ (λ A → ext _ _ (λ x → ext _ _ (λ p₁ → ext _ _ (λ p₂ → ext _ _
      (λ sq → f₂ A x p₁ p₂ sq)))))) )
  (λ f → z _)

c2t : S¹ → S¹ → Torus
c2t i j A x p₁ p₂ sq = ?

proj₁ : Torus → S¹
proj₁ z = ?

proj₂ : Torus → S¹
proj₂ z A x p = ?

