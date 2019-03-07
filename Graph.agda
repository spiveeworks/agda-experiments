open import Data.Nat as ℕ using (ℕ; _*_)
open import Data.Fin as Fin using (Fin)
open import Data.Bool as Bool using (Bool)
open import Data.Product using (_,_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)
open import Data.Product as Product using (∃-syntax)

open import Even using (Even; Odd; even; odd)

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

beginning : {ord length : ℕ} {g : Digraph ord} → Walk g length → Fin ord
beginning walk = Walk.steps walk (Fin.zero)

end : {ord length : ℕ} {g : Digraph ord} → Walk g length → Fin ord
end {length = length} walk = Walk.steps walk (Fin.fromℕ length)

IsClosed : {ord : ℕ} {g : Digraph ord} {length : ℕ} → Walk g length → Set
IsClosed walk = beginning walk ≡ end walk

-- closed walk is a cycle for now, since existence of odd cycles isnt affected
-- by this distinciton
record Cycle {ord : ℕ} (g : Digraph ord) (length : ℕ) : Set where
  field
    walk : Walk g length
    is-closed : IsClosed walk

EvenCycles : {ord : ℕ} → Digraph ord → Set
EvenCycles g = {length : ℕ} → Cycle g length → Even length

-- do i need some kind of structural induction on walks?
-- that would be nice but how do i structure walks to do that
-- does a vec instead of a table work? then just write an uncons function that
-- breaks the validity proof up as required... cons too? why not

--color-step : {ord : ℕ} → (g : Digraph ord) → (coloring : Coloring 2 g) →
  --{i j : Fin ord} → g i j ≡ Bool.True →
  --Coloring.map coloring i ≡ Coloring.map coloring j → ⊥
--color-step g coloring step color-eq = {!  !}

lemma-even : {ord : ℕ} → (g : Digraph ord) → (coloring : Coloring 2 g) →
  {length : ℕ} → ∀ (walk : Walk g length) → Even length →
  Coloring.map coloring (beginning walk) ≡ Coloring.map coloring (end walk)
lemma-even g coloring walk (r , refl) = {!   !}

lemma-odd : {ord : ℕ} → (g : Digraph ord) → (coloring : Coloring 2 g) →
  {length : ℕ} → ∀ (walk : Walk g length) → Odd length →
  Coloring.map coloring (beginning walk) ≡ Coloring.map coloring (end walk) → ⊥
lemma-odd g coloring walk (r , refl) color-eq = {!   !}

theorem₁ : {ord : ℕ} → (g : Digraph ord) → Coloring 2 g → EvenCycles g
theorem₁ g coloring {length} cycle with Even.decide length
... | even prf = prf
... | odd prf = ⊥-elim (lemma-odd g coloring (Cycle.walk cycle) prf eq-ends)
  where eq-ends = PropEq.cong (Coloring.map coloring) (Cycle.is-closed cycle)


theorem₂ : {ord : ℕ} → (g : Digraph ord) → EvenCycles g → Coloring 2 g
theorem₂ g even-cycles = ?

