open import Data.Nat as ℕ using (ℕ; _*_; _+_)
open import Data.Empty
open import Data.Fin as Fin using (Fin)
open import Data.Bool as Bool using (Bool)
open import Data.Product using (_,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

open import Graph
open import Even using (Even; Odd; even; odd)

open Coloring using (map)

EvenCycles : {ord : ℕ} → Digraph ord → Set
EvenCycles g = {length : ℕ} → Cycle g length → Even length

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
  open PropEq
  open ≡-Reasoning
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

color-alternate : {ord : ℕ} → (g : Digraph ord) → (c : Coloring 2 g) →
  (x y : Fin ord) → g x y ≡ Bool.true →
  map c x ≡ swap (map c y)
color-alternate g c x y x~y with decide-color (map c x) (map c y)
... | eq ceq with Coloring.contact c x y ceq
... | ()
color-alternate g c x y x~y | neq cneq = cneq

color-step : {ord : ℕ} → (g : Digraph ord) → (c : Coloring 2 g) →
  (x y z : Fin ord) → g x y ≡ Bool.true → g y z ≡ Bool.true →
  map c x ≡ map c z
color-step g c x y z x~y y~z =
  map c x               ≡⟨ color-alternate g c x y x~y ⟩
  swap (map c y)        ≡⟨ cong swap (color-alternate g c y z y~z) ⟩
  swap (swap (map c z)) ≡⟨ swap-swap ⟩
  map c z               ∎
  where
    open PropEq
    open ≡-Reasoning

{- Evenness theorem -}

lemma-step : {ord : ℕ} → (g : Digraph ord) → (c : Coloring 2 g) →
  {length : ℕ} → ∀ (walk : Walk g (2 + length)) →
  map c (beginning walk)
    ≡ map c (beginning (tail (tail walk)))
lemma-step g c walk = color-step g c x y z x~y y~z where
  x = beginning walk
  y = beginning (tail walk)
  z = beginning (tail (tail walk))
  x~y = Walk.valid walk Fin.zero
  y~z = Walk.valid walk (Fin.suc Fin.zero)

lemma-even : {ord : ℕ} → (g : Digraph ord) → (c : Coloring 2 g) →
  {length : ℕ} → ∀ (walk : Walk g length) → Even length →
  map c (beginning walk) ≡ map c (end walk)
lemma-even g c walk (ℕ.zero , refl) = refl
lemma-even g c walk (ℕ.suc r , refl) =
  map c (beginning walk) ≡⟨ lemma-step g c walk ⟩
  map c (beginning rest) ≡⟨ lemma-even g c rest (r , refl) ⟩
  map c (end walk) ∎
  where
    rest = tail (tail walk)
    open PropEq
    open ≡-Reasoning

lemma-odd : {ord : ℕ} → (g : Digraph ord) → (c : Coloring 2 g) →
  {length : ℕ} → ∀ (walk : Walk g length) → Odd length →
  map c (beginning walk) ≡ swap (map c (end walk))
lemma-odd g c walk (r , refl) =
  map c (beginning walk) ≡⟨ color-alternate g c (beginning walk) (beginning
                                 (tail walk)) (head walk) ⟩
  swap (map c (beginning (tail walk))) ≡⟨ cong swap (lemma-even g c
                                            (tail walk) (r , refl)) ⟩
  swap (map c (end walk)) ∎
  where
    open PropEq
    open ≡-Reasoning

lemma-odd′ : {ord : ℕ} → (g : Digraph ord) → (c : Coloring 2 g) →
  {length : ℕ} → ∀ (walk : Walk g length) → Odd length →
  map c (beginning walk) ≡ map c (end walk) → ⊥
lemma-odd′ g c walk len-odd ceq = swap-neq′ ceq (lemma-odd g c walk len-odd)

theorem₁ : {ord : ℕ} → (g : Digraph ord) → Coloring 2 g → EvenCycles g
theorem₁ g c {length} cycle with Even.decide length
... | even prf = prf
... | odd prf = ⊥-elim (lemma-odd′ g c (Cycle.walk cycle) prf eq-ends)
  where eq-ends = PropEq.cong (map c) (Cycle.is-closed cycle)

{- Color propositions for Coloring theorem -}

color-by-number : ℕ → Fin 2
color-by-number x with Even.decide x
... | even _ = Fin.zero
... | odd _ = Fin.suc Fin.zero

{- Coloring theorem -}

open _connected-to_within_ using (dist)

-- test if distance from zero is even, color by evenness
coloring-map : {ord : ℕ} (g : Digraph ord) → IsConnected g → Fin ord → Fin 2
coloring-map {ℕ.zero} g walks = λ ()
coloring-map {ℕ.suc _} g walks = color-by-number ∘ dist ∘ walks (Fin.zero)

coloring-contact : {ord : ℕ} (g : Digraph ord) →
  (walks : IsConnected g) → EvenCycles g →
  (x y : Fin ord) → coloring-map g walks x ≡ coloring-map g walks y →
  g x y ≡ Bool.true → ⊥
coloring-contact {ℕ.zero} g walks even-cycles ()
coloring-contact {ℕ.suc _} g walks even-cycles x y ceq edge =
  Even.contradict _ even-proof odd-proof where
    xc = walks Fin.zero x
    yc = walks y Fin.zero
    mw = fromEdge x y edge
    loopc = xc ++′ (mw ++′ yc)
    loop = fromConnected Fin.zero loopc
    even-proof = even-cycles loop
    odd-proof = ?

theorem₂ : {ord : ℕ} → (g : Digraph ord) →
  IsConnected g → EvenCycles g → Coloring 2 g
theorem₂ g walks even-cycles = coloring where
  coloring : Coloring 2 g
  Coloring.map coloring = coloring-map g walks
  Coloring.contact coloring x y ceq = elim (g x y) refl where
    -- neat little contravariance trick since I'm new to with-abstraction
    elim : (val : Bool) → g x y ≡ val → g x y ≡ Bool.false
    elim Bool.false ne = ne
    elim Bool.true e = ⊥-elim (coloring-contact g walks even-cycles x y ceq e)
