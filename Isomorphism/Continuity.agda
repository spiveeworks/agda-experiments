Type : Set₁
Type = Set

Kind : Set₂
Kind = Set₁

data _≡_ {l} {A : Set l} (x : A) : A → Set₀ where
  refl : x ≡ x

J : ∀ {l₁} {l₂} {A : Set l₁} (x : A) → (M : (y : A) → x ≡ y → Set l₂)
  → (M x refl) → (y : A) → (p : x ≡ y) → M y p
J x M m _ refl = m

cong : ∀ {l₁} {l₂} {A : Set l₁} {B : Set l₂} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong {x = x} f = J x (λ y p → f x ≡ f y) refl _

trans : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p₁ refl = p₁

Sphere : Kind
Sphere = ∀ M → (m : M) → m ≡ m → M

point : Sphere
point M m p = m

loop-pw : ∀ M → (m : M) → (p : m ≡ m) → point M m p ≡ point M m p
loop-pw M m p = p

postulate
  ext : ∀ {l₁} {l₂} {A : Set l₁} {B : A → Set l₂} (f g : (x : A) → B x)
    → ((x : A) → f x ≡ g x) → f ≡ g

loop : point ≡ point
loop = ext point point (λ M → ext (point M) (point M)
  (λ m → ext (point M m) (point M m) (λ p → p)))

postulate 
  ext-elim-J : ∀ {l₁} {l₂} {l₃} {A : Set l₁} {B : A → Set l₂}
    (f g : (x : A) → B x) → (pw : (x : A) → f x ≡ g x)
    → (x : A) → (M : (y : B x) → Set l₃)
    → (m : M (f x))
    → J f (λ f₀ _ → M (f₀ x)) m g (ext f g pw)
    ≡ J (f x) (λ y _ → M y) m (g x) (pw x)

ext-elim-cong : ∀ {l₁} {l₂} {A : Set l₁} {B : A → Set l₂} {C : Set}
  (f g : (x : A) → B x) → (pw : (x : A) → f x ≡ g x) → (x : A) → (h : B x → C)
  → cong (λ f₀ → h (f₀ x)) (ext f g pw) ≡ cong h (pw x)
ext-elim-cong f g pw x h = ext-elim-J f g pw x _ _

step₁ : ∀ {M} (m : M) (p : m ≡ m)
  → cong (λ x → x M m p) loop
  ≡ cong (λ xM → xM m p) (ext (point M) (point M)
    (λ m → ext (point M m) (point M m) (λ p → p)))
step₁ {M} m p = ext-elim-cong point point _ M (λ xM → xM m p)

step₂ : ∀ {M} (m : M) (p : m ≡ m)
  → cong (λ xM → xM m p) (ext (point M) (point M)
    (λ m → ext (point M m) (point M m) (λ p → p)))
  ≡ cong (λ xMm → xMm p) (ext (point M m) (point M m) (λ p → p))
step₂ {M} m p = ext-elim-cong _ _ _ m (λ xMm → xMm p)

step₃ : ∀ {M} (m : M) (p : m ≡ m)
  → cong (λ xMm → xMm p) (ext (point M m) (point M m) (λ p → p))
  ≡ cong (λ m₀ → m₀) p
step₃ {M} m p = ext-elim-cong _ _ _ p (λ m₀ → m₀)

step₄ : ∀ {M : Type} (m : M) (p : m ≡ m) → cong {A = M} {B = M} (λ m₀ → m₀) p ≡ p
step₄ m refl = refl

proposition : ∀ {M} (m : M) (p : m ≡ m) → cong (λ x → x M m p) loop ≡ p
proposition m p = trans (step₁ m p) (trans (step₂ m p) (trans (step₃ m p) (step₄ m p)))

