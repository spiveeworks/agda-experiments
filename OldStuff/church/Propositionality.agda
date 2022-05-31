
_≡_ : {A : Set} → A → A → Set₁
_≡_ {A} x y = ∀ (_~_ : A → A → Set) → (refl : {x₀ : A} → x₀ ~ x₀) → x ~ y

refl : {A : Set} → {x : A} → x ≡ x
refl {A} {x} _~_ refl′ = refl′ {x}


isPropositional : (A : Set) → Set₁
isPropositional A = ∀ {x y : A} → x ≡ y

isUnit : (A : Set) → A → Set₁
isUnit A x = ∀ {C : A → Set} → C x → ∀ (x′ : A) → C x′

unitFromProp : {A : Set} → (x : A) → isPropositional A → isUnit A x
unitFromProp x prop {C} m x′ = prop {x} {x′} (λ x y → C x → C y) (λ m → m) m

