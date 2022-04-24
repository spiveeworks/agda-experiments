open import Basics
open import Extensionality

Sphere : Kind
Sphere = ∀ M → (m : M) → m ≡ m → M

point : Sphere
point M m p = m

loop-pw : ∀ M → (m : M) → (p : m ≡ m) → point M m p ≡ point M m p
loop-pw M m p = p

loop : point ≡ point
loop = ext point point (λ M → ext (point M) (point M)
  (λ m → ext (point M m) (point M m) (λ p → p)))

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

