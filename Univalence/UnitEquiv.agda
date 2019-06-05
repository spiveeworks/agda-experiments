{-# OPTIONS --cubical #-}
open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Foundations.Isomorphism

_∋_ : ∀ {l} (A : Set l) → A → A
A ∋ x = x

refl : ∀ {l} {A : Set l} {x : A} → x ≡ x
refl {x = x} i = x

data ⊤ : Set where
  tt : ⊤

Deform : ∀ {l} → {A : Set l} {x y : A} → {p : x ≡ y} → PathP (λ j → x ≡ p j) refl p
Deform {p = p} i j = p (i ∧ j)

-- eureka moment
ΣDeform : ∀ {l} → {A : Set l} {x y : A} → {p : x ≡ y} →
  (Σ A (x ≡_)) ∋ (x , refl) ≡ (y , p)
ΣDeform {p = p} i = p i , Deform {p = p} i

-- K⊤ : ∀ {p : tt ≡ tt} → p ≡ refl
-- K⊤ {p} i j = ?

-- basic fiber reasoning

fiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ ⊔ ℓ')
fiber {A = A} f y = Σ A λ x → f x ≡ y

cong : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) {x₁ x₂ : A} →
  x₁ ≡ x₂ → f x₁ ≡ f x₂
cong f p i = f (p i)

mapFiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (x₁ x₂ : A) →
  (p : x₁ ≡ x₂) →  (x₁ , cong f p) ≡ (x₂ , refl {x = f x₂})
mapFiber f x₁ x₂ p i = p i , λ j → f (p (i ∨ j))

-- basic contraction reasoning

isProp : ∀ {ℓ} → Set ℓ → Set ℓ
isProp A = ∀ (x y : A) → x ≡ y

isContr : ∀ {ℓ} → Set ℓ → Set ℓ
isContr A = Σ A λ x → (∀ y → x ≡ y)

contract : ∀ {ℓ} → {A : Set ℓ} → A → isProp A → isContr A
contract x paths = x , paths x

unitProp : isProp ⊤
unitProp tt tt = refl

unitContr : isContr ⊤
unitContr = contract tt unitProp

-- isomorphism of contractible types

contrIso : ∀ {l l′} → {A : Set l} {B : Set l′} →
  isContr A → isContr B → Iso A B
contrIso (x , cx) (y , cy) = iso (λ _ → y) (λ _ → x) cy cx

contrEquiv : ∀ {l l′} → {A : Set l} {B : Set l′} →
  isContr A → isContr B → A ≃ B
contrEquiv cx cy = (λ _ → cy .fst) , isoToIsEquiv (contrIso cx cy)

contrPath : ∀ {l} → {A : Set l} {B : Set l} →
  isContr A → isContr B → A ≡ B
contrPath cx cy = isoToPath (contrIso cx cy)

