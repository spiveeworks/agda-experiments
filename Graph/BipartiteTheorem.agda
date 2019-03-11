open import Data.Nat as ℕ using (ℕ; _*_; _+_)
open import Data.Empty
open import Data.Fin as Fin using (Fin)
open import Data.Bool as Bool using (Bool)
open import Data.Product using (_,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Graph
open import Even using (Even; Odd; even; odd)

open Coloring using (map)

EvenCycles : {ord : ℕ} → Digraph ord → Set
EvenCycles {ord} g = {x : Fin ord} → (xx : Cycle g x) → Even (length xx)

{- Color propositions for Evenness theorem -}

swap : Fin 2 → Fin 2
swap Fin.zero = Fin.suc Fin.zero
swap (Fin.suc Fin.zero) = Fin.zero
swap (Fin.suc (Fin.suc ()))

swap-swap : ∀ {i : Fin 2} → swap (swap i) ≡ i
swap-swap {Fin.zero} = refl
swap-swap {Fin.suc Fin.zero} = refl
swap-swap {Fin.suc (Fin.suc ())}

swap-neq : ∀ {i : Fin 2} → i ≡ swap i → ⊥
swap-neq {Fin.zero} ()
swap-neq {Fin.suc Fin.zero} ()
swap-neq {Fin.suc (Fin.suc ())} _

swap-neq′ : ∀ {i j : Fin 2} → i ≡ j → i ≡ swap j → ⊥
swap-neq′ {i} {j} eq neq = swap-neq eq′ where
  eq′ =
    j      ≡⟨ sym eq ⟩
    i      ≡⟨ neq ⟩
    swap j ∎

data CDec (i j : Fin 2) : Set where
  eq : i ≡ j → CDec i j
  neq : i ≡ swap j → CDec i j

decide-color : ∀ (i j : Fin 2) → CDec i j
-- entire proof generated using split and auto
decide-color Fin.zero Fin.zero = eq refl
decide-color Fin.zero (Fin.suc Fin.zero) = neq refl
decide-color Fin.zero (Fin.suc (Fin.suc ()))
decide-color (Fin.suc Fin.zero) Fin.zero = neq refl
decide-color (Fin.suc Fin.zero) (Fin.suc Fin.zero) = eq refl
decide-color (Fin.suc Fin.zero) (Fin.suc (Fin.suc ()))
decide-color (Fin.suc (Fin.suc ())) j

color-step : {ord : ℕ} → (g : Digraph ord) → (c : Coloring 2 g) →
  (x y : Fin ord) → g x y ≡ Bool.true →
  map c x ≡ swap (map c y)
color-step g c x y x~y with decide-color (map c x) (map c y)
... | eq ceq with Coloring.contact c x y ceq
... | ()
color-step g c x y x~y | neq cneq = cneq

{- Evenness theorem -}

lemma₁-even : {ord : ℕ} → (g : Digraph ord) → (c : Coloring 2 g) →
  {x y : Fin ord} → ∀ (xy : Walk g x y) → Even (length xy) →
  map c x ≡ map c y
lemma₁-odd : {ord : ℕ} → (g : Digraph ord) → (c : Coloring 2 g) →
  {x y : Fin ord} → ∀ (xy : Walk g x y) → Odd (length xy) →
  map c x ≡ swap (map c y)
lemma₁-even g c finish leven = refl
lemma₁-even g c {x} {y} (step {x′} xx′ x′y) leven =
  map c x ≡⟨ color-step g c x x′ xx′ ⟩
  swap (map c x′) ≡⟨ cong swap (lemma₁-odd g c x′y (Even.even-back leven)) ⟩
  swap (swap (map c y)) ≡⟨ swap-swap ⟩
  map c y ∎
lemma₁-odd g c finish (r , ())
lemma₁-odd g c {x} {y} (step {x′} xx′ x′y) lodd =
  map c x ≡⟨ color-step g c x x′ xx′ ⟩
  swap (map c x′) ≡⟨ cong swap (lemma₁-even g c x′y (Even.odd-back lodd)) ⟩
  swap (map c y) ∎

lemma₁-odd′ : {ord : ℕ} → (g : Digraph ord) → (c : Coloring 2 g) →
  {x y : Fin ord} → ∀ (xy : Walk g x y) → Odd (length xy) →
  map c x ≡ map c y → ⊥
lemma₁-odd′ g c walk len-odd ceq = swap-neq′ ceq (lemma₁-odd g c walk len-odd)

theorem₁ : {ord : ℕ} → (g : Digraph ord) → Coloring 2 g → EvenCycles g
theorem₁ g c cycle with Even.decide (length cycle)
... | even prf = prf
... | odd prf = ⊥-elim (lemma₁-odd′ g c cycle prf refl)

{- Color propositions for Coloring theorem -}

color-by-number : ℕ → Fin 2
color-by-number x with Even.decide x
... | even _ = Fin.zero
... | odd _ = Fin.suc Fin.zero

{- Coloring theorem -}

-- test if distance from zero is even, color by evenness
coloring-map : {ord : ℕ} (g : Digraph ord) → IsConnected g → Fin ord → Fin 2
coloring-map {ℕ.zero} g walks = λ ()
coloring-map {ℕ.suc _} g walks = color-by-number ∘ length ∘ walks (Fin.zero)

lemma₂-odd : {ord : ℕ} (g : Digraph ord) → {x y₁ y₂ z : Fin ord} →
  (xy₁ : Walk g x y₁) → (y₁y₂ : g y₁ y₂ ≡ Bool.true) → (y₂z : Walk g y₂ z) →
  Even.SameEvenness (length xy₁) (length y₂z) →
  Odd (length (xy₁ ++ step y₁y₂ y₂z))
lemma₂-odd g xy₁ y₁y₂ y₂z se = subst Odd (sym (++-len xy₁ (step y₁y₂ y₂z)))
  (Even.different-sum′ se)

coloring-evenness : {ord : ℕ} (g : Digraph (ℕ.suc ord)) →
  (gsym : IsGraph g) → (walks : IsConnected g) →
  ∀ (x y : Fin (ℕ.suc ord)) → coloring-map g walks x ≡ coloring-map g walks y →
  Even.SameEvenness
    (length (walks Fin.zero x))
    (length (reverse gsym (walks Fin.zero y)))
coloring-evenness g gsym walks x y ceq
  with Even.decide (length (walks Fin.zero x))
  | Even.decide (length (walks Fin.zero y))
... | even zxe | even (r , yze) = even zxe (r , zye) where
  zye =
    length (reverse gsym (walks Fin.zero y)) ≡⟨ reverse-len gsym (walks Fin.zero y) ⟩
    length (walks Fin.zero y) ≡⟨ yze ⟩
    r * 2 ∎
coloring-evenness g gsym walks x y () | even zxe | odd yzo
coloring-evenness g gsym walks x y () | odd zxo | even yze
... | odd zxo | odd (r , yzo) = odd zxo (r , zyo) where
  zyo =
    length (reverse gsym (walks Fin.zero y)) ≡⟨ reverse-len gsym (walks Fin.zero y) ⟩
    length (walks Fin.zero y) ≡⟨ yzo ⟩
    1 + r * 2 ∎

coloring-contact : {ord : ℕ} (g : Digraph ord) →
  IsGraph g → (walks : IsConnected g) → EvenCycles g →
  (x y : Fin ord) → coloring-map g walks x ≡ coloring-map g walks y →
  g x y ≡ Bool.true → ⊥
coloring-contact {ℕ.zero} g gsym walks even-cycles ()
coloring-contact {ℕ.suc _} g gsym walks even-cycles x y ceq edge =
  Even.contradict _ even-proof odd-proof where
    xc = walks Fin.zero x
    yc = reverse gsym (walks Fin.zero y)
    loop = xc ++ (Walk.step edge yc)
    even-proof = even-cycles loop
    odd-proof = lemma₂-odd g xc edge yc
      (coloring-evenness g gsym walks x y ceq)

theorem₂ : {ord : ℕ} → (g : Digraph ord) →
  IsGraph g → IsConnected g → EvenCycles g → Coloring 2 g
theorem₂ g gsym walks even-cycles = coloring where
  coloring : Coloring 2 g
  Coloring.map coloring = coloring-map g walks
  Coloring.contact coloring x y ceq = elim (g x y) refl where
    -- neat little contravariance trick since I'm new to with-abstraction
    elim : (val : Bool) → g x y ≡ val → g x y ≡ Bool.false
    elim Bool.false ne = ne
    elim Bool.true e = ⊥-elim (coloring-contact g gsym walks even-cycles x y ceq e)
