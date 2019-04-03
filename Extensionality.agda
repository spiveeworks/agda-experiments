open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as HetEq

module Extensionality where

--extensionalEq : {A B : Set} → (f g : A → B) → (p : (x : A) → f x ≡ g x) →
    --HetEq._≅_ (λ x → p x)  (λ x → refl {_} {B} {f x})
--extensionalEq f g p = refl

module Lambda where
    Id : Set → Set
    Id T = T → T

    id1 : ∀ (T : Set) → Id T
    id1 T = λ x → x

    id2 : ∀ (T : Set) → Id T
    id2 T y = y

    lambda-test : id1 ≡ id2
    lambda-test = refl

    eta : {A B : Set} → ∀ (f : A → B) → f ≡ (λ x → f x)
    eta f = refl


open import Data.Bool as Bool using (Bool)

if_then_else_ : {B : Set} → Bool → B → B → B
if Bool.true then x else y = x
if Bool.false then x else y = y

ext-beq : {B : Set} → ∀ (f : Bool → B) → ∀ (x : Bool) →
    f x ≡ if x then f Bool.true else f Bool.false
ext-beq f Bool.false = refl
ext-beq f Bool.true = refl

--eta-beq : {B : Set} → ∀ (f : Bool → B) →
    --(λ x → f x) ≡ (λ x → if x then (f Bool.true) else (f Bool.false))
--eta-beq f = ?
