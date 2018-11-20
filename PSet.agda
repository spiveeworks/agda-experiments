module PSet where

open import Data.Product as Product hiding (proj₁; proj₂)
import Data.Sum as Sum
open Sum using (_⊎_)

Pred : Set → Set₁
Pred U = U → Set

_and_ : Set → Set → Set
_and_ = Product._×_

PSet : {U : Set} (P : Pred U) → Set
PSet P = ∃[ x ] P x

_∪_ : {U : Set} (S₁ S₂ : Pred U) → Pred U
S₁ ∪ S₂ = λ x → S₁ x ⊎ S₂ x

inj₁ : {U : Set} {S₁ S₂ : Pred U} → PSet S₁ → PSet (S₁ ∪ S₂)
inj₁ = map₂ Sum.inj₁

inj₂ : {U : Set} {S₁ S₂ : Pred U} → PSet S₂ → PSet (S₁ ∪ S₂)
inj₂ = map₂ Sum.inj₂


_∩_ : {U : Set} (S₁ S₂ : Pred U) → Pred U
S₁ ∩ S₂ = λ x → S₁ x and S₂ x

proj₁ : {U : Set} {S₁ S₂ : Pred U} → PSet (S₁ ∩ S₂) → PSet S₁
proj₁ = map₂ Product.proj₁

proj₂ : {U : Set} {S₁ S₂ : Pred U} → PSet (S₁ ∩ S₂) → PSet S₂
proj₂ = map₂ Product.proj₂


