open import Data.Nat as ℕ using (ℕ; _*_)
open import Data.Fin as Fin using (Fin)
open import Data.Bool as Bool using (Bool)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Data.Product as Product using (∃-syntax)

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
  field
    steps : Fin (ℕ.suc length) → Fin ord
    valid : ∀ (i : Fin length) →
      g (steps (Fin.inject₁ i)) (steps (Fin.suc i)) ≡ Bool.true

IsClosed : {ord : ℕ} {g : Digraph ord} {length : ℕ} → Walk g length → Set
IsClosed {length = length} walk = steps Fin.zero ≡ steps (Fin.fromℕ length)
  where steps = Walk.steps walk

-- closed walk is a cycle for now, since existence of odd cycles isnt affected
-- by this distinciton
record Cycle {ord : ℕ} (g : Digraph ord) (length : ℕ) : Set where
  field
    walk : Walk g length
    is-closed : IsClosed walk

NoOddCycles : {ord : ℕ} → Digraph ord → Set
NoOddCycles g = {length : ℕ} → Cycle g length → ∃[ n ] (length ≡ n * 2)

theorem₁ : {ord : ℕ} → (g : Digraph ord) → Coloring 2 g → NoOddCycles g
theorem₁ g coloring cycle = ?

theorem₂ : {ord : ℕ} → (g : Digraph ord) → NoOddCycles g → Coloring 2 g
theorem₂ g no-odd-cycles = ?

