open import Data.Nat as ℕ using (ℕ; _*_; _+_)
open import Data.Fin as Fin using (Fin)
open import Data.Bool as Bool using (Bool)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

-- simple digraph with loops
Digraph : (ord : ℕ) → Set
Digraph ord = Fin ord → Fin ord → Bool

IsGraph : {ord : ℕ} → Digraph ord → Set
IsGraph {ord} g = ∀ (x y : Fin ord) → g x y ≡ g y x

record Graph (ord : ℕ) : Set where
  field
    edge : Digraph ord
    sym : IsGraph edge

record Coloring {ord : ℕ} (colors : ℕ) (g : Digraph ord) : Set where
  field
    map : Fin ord → Fin colors
    contact : ∀ (x y : Fin ord) → map x ≡ map y → g x y ≡ Bool.false

data Walk {ord : ℕ} (g : Digraph ord) (x : Fin ord) : Fin ord → Set where
  finish : Walk g x x
  step : {x′ y : Fin ord} →
    g x x′ ≡ Bool.true → Walk g x′ y → Walk g x y

-- not maintained since new walk repr
{-
tail : {ord length : ℕ} {g : Digraph ord} → Walk g (1 + length) → Walk g length
tail (vs via es) = (λ i → vs (Fin.suc i)) via (λ i → es (Fin.suc i))

head : {ord length : ℕ} {g : Digraph ord} → (walk : Walk g (1 + length)) →
  g (beginning walk) (beginning (tail walk)) ≡ Bool.true
head (vs via es) = es Fin.zero

reverse : {ord length : ℕ} {g : Digraph ord} → IsGraph g → Walk g length →
  Walk g length
reverse {ord} {length} {g} sym (steps via edges) = (steps ∘ invert) via
  (λ i →
    g (steps (invert (Fin.inject₁ i))) (steps (Fin.inject₁ (invert i)))
      ≡⟨ sym _ _ ⟩
    g (steps (Fin.inject₁ (invert i))) (steps (invert (Fin.inject₁ i)))
      ≡⟨ cong (λ i′ → g (steps (Fin.inject₁ (invert i))) (steps i′)) (invert-lemma i) ⟩
    g (steps (Fin.inject₁ (invert i))) (steps (Fin.suc (invert i)))
      ≡⟨ edges (invert i) ⟩
    Bool.true ∎
  ) where
  open PropEq hiding (sym)
  open ≡-Reasoning
  invert : {n : ℕ} → Fin n → Fin n
  invert {ℕ.suc n} Fin.zero = Fin.fromℕ n
  invert {ℕ.suc n} (Fin.suc x) = Fin.inject₁ (invert x)
  invert-lemma : {n : ℕ} → ∀ (i : Fin n) →
    invert (Fin.inject₁ i) ≡ Fin.suc (invert i)
  invert-lemma Fin.zero = refl
  invert-lemma (Fin.suc i) = cong Fin.inject₁ (invert-lemma i)
-}

-- closed walk is a cycle for now, since existence of odd cycles isnt affected
-- by this distinciton
Cycle : {ord : ℕ} (g : Digraph ord) (x : Fin ord) → Set
Cycle g x = Walk g x x

IsConnected : {ord : ℕ} (g : Digraph ord) → Set
IsConnected {ord} g = ∀ (x y : Fin ord) → Walk g x y


_++_ : {ord : ℕ} {g : Digraph ord} → ∀ {x y z : Fin ord} →
  Walk g x y → Walk g y z → Walk g x z
finish ++ yz = yz
(step wx xy) ++ yz = step wx (xy ++ yz)


length : {ord : ℕ} {g : Digraph ord} {x y : Fin ord} → Walk g x y → ℕ
length finish = 0
length (step wx xy) = 1 + length xy
