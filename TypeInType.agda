{-# OPTIONS --type-in-type #-}

Problem : Set
Problem = (A : Set) → ((B : Set) → (B → B → Set) → A) → A

inj : (A : Set) → (A → A → Set) → Problem
inj A R A′ P = P A R

_≡_ : {A : Set} → A → A → Set
_≡_ {A} x y = ∀ (C : A → Set) → C x → C y

∃ : {A : Set} → (A → Set) → Set
∃ {A} B = (C : Set) → ((x : A) → B x → C) → C

_,_ : {A : Set} {B : A → Set} → (x : A) → B x → ∃ B
_,_ x y C m = m x y

Morph : (A : Set) → (R : A → A → Set) → (B : Set) → (S : B → B → Set) → Set
Morph A R B S = ∃ λ (f : A → B) → ∀ x y → R x y → S (f x) (f y)

morph-id : (A : Set) → (R : A → A → Set) → Morph A R A R
morph-id A R = (λ x → x) , (λ x y p → p)

lemma : ∀ A R B S → inj A R ≡ inj B S → Morph A R B S
lemma A R B S eq = eq (λ x → x Set (λ D → λ T → Morph A R D T)) (morph-id A R)


List : Set → Set
List A = (B : Set) → (A → B → B) → B → B

empty : {A : Set} → List A
empty B f y = y

cons : {A : Set} → A → List A → List A
cons x xs B f y = f x (xs B f y)



Tree : Set
Tree = (B : Set) → (B → B → B) → B → B

buildTree : List Tree → Tree
buildTree ts B f y = ts B (λ t y′ → f (t B f y) y′) y


