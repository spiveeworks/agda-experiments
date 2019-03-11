open import Data.Nat as ℕ using (ℕ; _*_; _+_)
import Data.Nat.Properties
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

reverse-helper : {ord : ℕ} {g : Digraph ord} → IsGraph g →
  {x y z : Fin ord} → Walk g x y → Walk g x z → Walk g y z
reverse-helper gsym finish xz = xz
reverse-helper {g = g} gsym {x} (step {x′} xx′ x′y) xz =
  reverse-helper gsym x′y x′z where
  x′z = step x′x xz where
    open PropEq
    open ≡-Reasoning
    x′x =
      g x′ x ≡⟨ gsym x′ x ⟩
      g x x′ ≡⟨ xx′ ⟩
      Bool.true ∎

reverse : {ord : ℕ} {g : Digraph ord} → IsGraph g →
  {x y : Fin ord} → Walk g x y → Walk g y x
reverse {ord} {g} gsym xy = reverse-helper gsym xy finish

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

reverse-helper-len : {ord : ℕ} {g : Digraph ord} → (gsym : IsGraph g) →
  {x y z : Fin ord} → (xy : Walk g x y) → (xz : Walk g x z) →
  length (reverse-helper gsym xy xz) ≡ length xy + length xz
reverse-helper-len _ finish xz = refl
reverse-helper-len _ (step x₁ xy) xz =
  PropEq.trans (reverse-helper-len _ xy _) (Data.Nat.Properties.+-suc _ _)

reverse-len : {ord : ℕ} {g : Digraph ord} → (gsym : IsGraph g) →
  {x y : Fin ord} → (xy : Walk g x y) → length (reverse gsym xy) ≡ length xy
reverse-len gsym xy = PropEq.trans (reverse-helper-len gsym xy finish) (Data.Nat.Properties.+-identityʳ _)

++-len : {ord : ℕ} {g : Digraph ord} →
  ∀ {x y z : Fin ord} → (xy : Walk g x y) (yz : Walk g y z) →
  length (xy ++ yz) ≡ length xy + length yz
++-len finish yz = refl
++-len (step _ x′y) yz = PropEq.cong ℕ.suc (++-len x′y yz)

