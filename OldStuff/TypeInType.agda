{-# OPTIONS --type-in-type #-}
-- attempting Hurksens's approach

U : Set
-- note this is positive in Set, so in some sense 'contains' a Set
-- BUT if we disqualify this term for that reason alone, then we also lose
-- (Bool → A) → A =β (((C : Set) → ...) → A) → A
--U = ∀ (X : Set) → ((X → Set) → X) → X
-- but for now we try the following, which is already a Kind since it returns a
-- Type directly
U = ∀ (X : Set) → ((X → Set) → X) → X → Set

τ : (U → Set) → U
τ X A c a = ∀ (P : A → Set) → (∀ x → X x → P (c (x A c))) → P a

σ : U → (U → Set)
σ x = x U τ

-- U is paradoxical iff ∀ X → σ (τ X) = { τ (σ x′) | X x′ }
-- i.e. ∀ x → σ (τ X) x <=> ∃ x′ : X x′ ∧ x ≡ τ (σ x′)
-- in backwards direction that means X x′ => σ (τ X) (τ (σ x′))
paradoxical-bwd : (X : U → Set) → ∀ x → X x → σ (τ X) (τ (σ x))
-- τ X U τ (τ (σ x))
-- P → (∀ x → X x → P (τ ((x U) τ))) → P (τ (σ x))
paradoxical-bwd X x elem P prf = prf x elem

-- in forwards direction it means f : σ (τ X) x -> U
-- along with X (f(x, _)), and
-- x ≡ τ (σ (f(x, _)))
--   ≡ λ A c a → ∀ (P : A → Set) → (∀ x′ → f(x, _) U τ x′ → P (c (x′ A c))) → P a
-- RHS (x A c) ? : x A c a
-- ? : ∀ x′ → f(x, _) U τ x′ → x A c (c (x′ A c))
paradoxical : (X : U → Set) → (x : U) → σ (τ X) x → U
paradoxical X x prf U₁ τ₁ x₁ = ?

paradoxical-fwd : ∀ X x prf → X (paradoxical X x prf)
paradoxical-fwd = ?

_<_ : U → U → Set
x < y = σ y x

Inductive : (U → Set) → Set
Inductive X = ∀ x → (∀ y → y < x → X y) → X x

WellFounded : U → Set
WellFounded x = ∀ X → Inductive X → X x

Ω : U
Ω = τ WellFounded

τ∘σ-continuous : ∀ x y → y < x → τ (σ y) < τ (σ x)
τ∘σ-continuous x y lss P z = z y lss

lemma : ∀ X → Inductive X → (x : U) → (∀ y → y < x → X (τ (σ y))) → X (τ (σ x))
lemma X indX x preds = indX (τ (σ x)) (λ y lss → lss X preds)

ords-wf : WellFounded Ω
ords-wf X indX = indX Ω (λ y lss → ?)

