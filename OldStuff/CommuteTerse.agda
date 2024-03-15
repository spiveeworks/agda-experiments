Type : Set1
Type = Set

infix 4 _≡_

data _≡_ {A : Type} (x : A) : A → Type where
  refl : x ≡ x

cong : {A B : Type} → (f : A → B) → {x₁ x₂ : A} → x₁ ≡ x₂ → f x₁ ≡ f x₂
cong f refl = refl

trans : {A : Type} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p refl = p

data Nat : Type where
  zero : Nat
  suc : Nat → Nat

infixl 6 _+_

_+_ : Nat → Nat → Nat
x + zero = x
x + (suc y) = suc (x + y)

commute-zero : (x : Nat) → x + zero ≡ zero + x
-- both sides are zero + zero
commute-zero zero = refl
-- left side is (suc x) + zero, which evaluates to suc x,
-- right side is zero + (suc x), which evaluates to suc (zero + x),
-- by recursing we can prove x ≡ (zero + x),
-- so recurse, and then apply suc to both sides
commute-zero (suc x) = cong suc (commute-zero x)

commute-suc : (x : Nat) → (y : Nat) → x + (suc y) ≡ (suc x) + y
-- both sides evaluate to suc x
commute-suc x zero = refl
-- left side is x + (suc (suc y)), i.e. suc (suc (x + y)),
-- right side is (suc x) + (suc y) i.e. suc ((suc x) + y)
-- but by recursing we prove that suc (x + y) ≡ (suc x) + y
-- so apply suc to both sides.
commute-suc x (suc y) = cong suc (commute-suc x y)

commute : (x : Nat) → (y : Nat) → x + y ≡ y + x
commute x zero = commute-zero x
-- left side is x + (suc y) which evaluates to suc (x + y),
-- right side is (suc y) + x which doesn't evaluate any further,
-- we can recurse to show that x + y = y + x,
-- then we can apply suc to both sides to get suc (x + y) = suc (y + x)
-- then we can also use commue-suc to show suc (y + x) = (suc y) + x
-- put these together and we have shown suc (x + y) = (suc y) + x
commute x (suc y) = trans (cong suc (commute x y)) (commute-suc y x)

commute-fn : (f : Nat → Nat) → (g : Nat → Nat) → (i : Nat) → f i + g i ≡ g i + f i
commute-fn f g i = commute (f i) (g i)

commute-poly : (A : Type) → (f : A → Nat) → (g : A → Nat) → (i : A) → f i + g i ≡ g i + f i
commute-poly A f g i = commute (f i) (g i)

commute-poly2 : (A : Type) → (B : Type) → (f : A → Nat) → (g : B → Nat) → (i : A) → (j : B) → f i + g j ≡ g j + f i
commute-poly2 A B f g i j = commute (f i) (g j)

