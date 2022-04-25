open import Basics

infixr 6 _$_
infixr 5 _++_ -_ _+-_

_++_ = trans
_$_ = cong
-_ = sym

_+-_ : ∀ {A : Type} → {x y z : A} → x ≡ y → z ≡ y → x ≡ z
p₁ +- p₂ = p₁ ++ (- p₂)

dist : ∀ {A B : Type} {x y z : A} (f : A → B) (p₁ : x ≡ y) (p₂ : y ≡ z)
  → f $ (p₁ ++ p₂) ≡ f $ p₁ ++ f $ p₂
dist f p₁ refl = refl

assoc : ∀ {A : Type} {w x y z : A} (p₁ : w ≡ x) (p₂ : x ≡ y) (p₃ : y ≡ z)
  → (p₁ ++ p₂) ++ p₃ ≡ p₁ ++ p₂ ++ p₃
assoc p₁ p₂ refl = refl

inv : ∀ {A} {x y : A} (p : x ≡ y) → p +- p ≡ refl
inv refl = refl

left-ident : ∀ {A : Type} {x y : A} (p : x ≡ y) → refl ++ p ≡ p
left-ident refl = refl

neg-dist : ∀ {A} {x y z : A} (p₁ : x ≡ y) (p₂ : y ≡ z)
  →  (- p₂) ++ (- p₁) ≡ - (p₁ ++ p₂)
neg-dist p₁ refl = left-ident (- p₁)

transp-decomp : {A B : Type} (f₁ f₂ : A → B) {x₁ x₂ : A}
  → (px : x₁ ≡ x₂) (pf : f₁ x₁ ≡ f₂ x₁)
  → transp (λ x → f₁ x ≡ f₂ x) px pf
  ≡ (- f₁ $ px) ++ pf ++ f₂ $ px
transp-decomp f₁ f₂ refl pf = - left-ident pf
