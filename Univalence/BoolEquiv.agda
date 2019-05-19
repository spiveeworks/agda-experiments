{-# OPTIONS --cubical #-}
open import Cubical.Core.Everything
open import Agda.Builtin.Nat as ℕ renaming (Nat to ℕ)

refl : ∀ {l} {A : Set l} {x : A} → x ≡ x
refl {x = x} i = x

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data Bool : Set where
  true : Bool
  false : Bool

data IsTrue : Bool → Set where
  tt : IsTrue true

partialBool : ∀ i → Partial (i ∨ ~ i) Bool
partialBool i = λ { (i = i0) → false; (i = i1) → true }

truthProof : ∀ {x} → true ≡ x → IsTrue x
truthProof p = transp (λ i → IsTrue (p i)) i0 tt

absurd₁ : true ≡ false → ⊥
absurd₁ p with truthProof p
absurd₁ p | ()

absurd₂ : false ≡ true → ⊥
absurd₂ p = absurd₁ (λ i → p (~ i))

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc : ∀ {n} → Fin n → Fin (suc n)

isSuc : ∀ {n} → Fin n → Bool
isSuc zero = false
isSuc (suc x) = true

fromFin : Fin 2 → Bool
fromFin = isSuc

toFin : Bool → Fin 2
toFin false = zero
toFin true = suc zero

coBoolElim : ∀ {l} {C : Bool → Set l} {A : Set l} →
  (C true → A) → (C false → A) →
  ∀ {x} → C x → A
coBoolElim mt mf {true} = mt
coBoolElim mt mf {false} = mf

Ktrue : ∀ {p : true ≡ true} → p ≡ refl
Ktrue {p} i j = coBoolElim {C = true ≡_} {A = Bool}
  (λ j′ → ?)
  (λ p → ⊥-elim (absurd₁ p))
  ? --(λ j′ → p (j ∧ j′))

iso : isEquiv fromFin
equiv-proof iso y = (toFin y , λ i → ?) , ?
{-
equiv-proof iso true = ((suc zero , refl) , contract) where
  contract : ∀ x → (suc zero , refl) ≡ x
  contract (zero , false≡true) = ⊥-elim (absurd₂ false≡true)
  contract (suc zero , p) i =  , λ j → p (~ i ∨ j)
  contract (suc (suc ()) , _)
equiv-proof iso false = ((zero , refl) , λ x → ?)
-}


idfun : ∀ {ℓ} → (A : Set ℓ) → A → A
idfun _ x = x

idLemma : ∀ {l} {A : Set l} → (x₁ : A) → (z : Σ A λ x₂ → x₂ ≡ x₁) → (x₁ , refl) ≡ z
idLemma x₁ z i = z .snd (~ i) , λ j → z .snd (~ i ∨ j)
--idLemma x₁ z = idIsEquiv _ .equiv-proof x₁ .snd z

idIsEquiv : ∀ {ℓ} (A : Set ℓ) → isEquiv (idfun A)
equiv-proof (idIsEquiv A) y =
  ((y , refl) , idLemma y)

idEquiv : ∀ {ℓ} (A : Set ℓ) → A ≃ A
idEquiv A = (idfun A , idIsEquiv A)

