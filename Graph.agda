open import Data.Nat as ℕ using (ℕ; _*_; _+_)
open import Data.Fin as Fin using (Fin)
open import Data.Bool as Bool using (Bool)
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

IsClosed : {ord : ℕ} {g : Digraph ord} {length : ℕ} → Walk g length → Set
IsClosed walk = beginning walk ≡ end walk

-- closed walk is a cycle for now, since existence of odd cycles isnt affected
-- by this distinciton
record Cycle {ord : ℕ} (g : Digraph ord) (length : ℕ) : Set where
  field
    walk : Walk g length
    is-closed : IsClosed walk

