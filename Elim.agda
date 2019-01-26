open import Data.Product
open import Function

Congruent : {A : Set} → (A → A → Set) → Set₂
Congruent {A} _≅_ = (P : (x : A) (y : A) → Set₁) →
  ({x : A} → P x x) →
  (x y : A) → (e : x ≅ y) → P x y

sigmaEq : {A : Set} → {B : A → Set} →
  (_≅A_ : A → A → Set) → ({x : A} → B x → B x → Set) →
  Congruent _≅A_ → Σ A B → Σ A B → Set
sigmaEq {A} {B} _≅A_ _≅B_ J (x₁ , y₁) (x₂ , y₂) = Σ[ eqx ∈ (x₁ ≅A x₂) ]
    (J P _≅B_ x₁ x₂ eqx y₁ y₂) where

  P : A → A → Set₁
  P x₁′ x₂′ = B x₁′ → B x₂′ → Set


module Test where
  open import Data.Empty
  open import Data.Unit
  open import Data.Bool

  _≅⊤_ : ⊤ → ⊤ → Set
  tt ≅⊤ tt = ⊤

  J⊤ : Congruent _≅⊤_
  J⊤ P p tt tt tt = p

  _≅Bool_ : Bool → Bool → Set
  true ≅Bool true = ⊤
  true ≅Bool false = ⊥
  false ≅Bool false = ⊤
  false ≅Bool true = ⊥

  JBool : Congruent _≅Bool_
  JBool P p true true tt = p {true}
  JBool P p true false ()
  JBool P p false false tt = p {false}
  JBool P p false true ()

  TyFam : Bool → Set
  TyFam true = Bool
  TyFam false = ⊤

  Ty : Set
  Ty = Σ Bool TyFam

  _≅TyFam_ : {x : Bool} → TyFam x → TyFam x → Set
  _≅TyFam_ {true} = _≅Bool_
  _≅TyFam_ {false} = _≅⊤_

  _≅Ty_ : Ty → Ty → Set
  _≅Ty_ = sigmaEq _≅Bool_ _≅TyFam_ JBool

  egjt : (true , true) ≅Ty (true , true)
  egjt = (tt , tt)

  egn : (false , tt) ≅Ty (false , tt)
  egn = (tt , tt)

  egp1 : (false , tt) ≅Ty (true , true) → ⊥
  egp1 (() , _)

  egp2 : (true , false) ≅Ty (true , true) → ⊥
  egp2 (tt , ())
