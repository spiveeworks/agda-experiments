open import Data.Nat as ℕ using (ℕ; _*_; _+_)
open import Data.Fin as Fin using (Fin)
open import Data.Bool as Bool using (Bool)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

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

record Walk {ord : ℕ} (g : Digraph ord) (length : ℕ) : Set where
  constructor _via_
  field
    steps : Fin (ℕ.suc length) → Fin ord
    valid : ∀ (i : Fin length) →
      g (steps (Fin.inject₁ i)) (steps (Fin.suc i)) ≡ Bool.true

beginning : {ord length : ℕ} {g : Digraph ord} → Walk g length → Fin ord
beginning walk = Walk.steps walk (Fin.zero)

end : {ord length : ℕ} {g : Digraph ord} → Walk g length → Fin ord
end {length = length} walk = Walk.steps walk (Fin.fromℕ length)

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

IsClosed : {ord : ℕ} {g : Digraph ord} {length : ℕ} → Walk g length → Set
IsClosed walk = beginning walk ≡ end walk

-- closed walk is a cycle for now, since existence of odd cycles isnt affected
-- by this distinciton
record Cycle {ord : ℕ} (g : Digraph ord) (length : ℕ) : Set where
  field
    walk : Walk g length
    is-closed : IsClosed walk

record _connected-to_within_ {ord : ℕ} (x y : Fin ord) (g : Digraph ord) : Set
  where
  field
    dist : ℕ
    walk : Walk g dist
    b≡x : beginning walk ≡ x
    e≡y : end walk ≡ y

IsConnected : {ord : ℕ} (g : Digraph ord) → Set
IsConnected {ord} g = ∀ (x y : Fin ord) → x connected-to y within g


