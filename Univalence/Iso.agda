{-# OPTIONS --cubical #-}
open import Agda.Primitive
open import Cubical.Core.Everything

refl : ∀ {a} {A : Set a} {x : A} → x ≡ x
refl {x = x} i = x

_IsLeftInverseOf_ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (g : B → A) → Set b
f IsLeftInverseOf g = ∀ y → f (g y) ≡ y

record _↔_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    fwd : A → B
    bwd : B → A
    surj : fwd IsLeftInverseOf bwd
    inj : bwd IsLeftInverseOf fwd

open _↔_

fromEquiv : ∀ {a b} {A : Set a} {B : Set b} → A ≃ B → A ↔ B
fromEquiv {A = A} {B = B} e = iso where
  map = e .fst
  equiv = e .snd .equiv-proof
  iso : A ↔ B
  iso .fwd = map
  iso .bwd y = equiv y .fst .fst
  iso .surj y = equiv y .fst .snd
  iso .inj x i = equiv (map x) .snd (x , λ j → map x) i .fst

mapFibers : ∀ {a b} {A : Set a} {B : Set b} → (f : A → B) → (y : B) →
  (z₁ z₂ : Σ A λ x → f x ≡ y) → z₁ .fst ≡ z₂ .fst → z₁ ≡ z₂
mapFibers f y z₁ z₂ p i = p i , λ j → hcomp
  (λ h → λ { (j = i0) → f (p i) ; (j = i1) → z₂ .snd h })
  (f (p (i ∨ j)))
--λ j₁ → hcomp (λ j₂ → λ { (i = i0) → z₁ .snd j₂ ; (i = i1) → z₂ .snd j₂ }) (f (p i))
--λ j → hfill (λ _ → λ { (i = i0) → z₁ .snd ? ; (i = i1) → z₂ .snd ? }) (inS (f (p i))) ?
--hcomp (λ j → λ { (i = i0) → z₁ .snd ; (i = i1) → z₂ .snd}) (f (p i))

fromIso : ∀ {a b} {A : Set a} {B : Set b} → A ↔ B → A ≃ B
fromIso {A = A} {B = B} iso = iso .fwd , eq where
  eq : isEquiv (iso .fwd)
  eq .equiv-proof y = centre , contract where
    centre = iso .bwd y , iso .surj y
    contract : ∀ (z : Σ A λ x → iso .fwd x ≡ y) → centre ≡ z
    contract z = ?
{-
primarily need a path between iso .bwd y, and z .fst
but along this path we would need fibers from f (p i) to y
and on top of that the endpoints of our fibers would need to be
iso .surj y, and z .snd
well our path from iso .bwd y to z .fst would be...
z .snd : fwd (z .fst) ≡ y
cong bwd (z .snd) : bwd (fwd (z .fst)) ≡ bwd y
inj (z .fst) : bwd (fwd (z .fst)) ≡ z .fst
so if we composed those we'd have a path between z .snd and bwd y
so their midpoint might be where we want to map our fibers
x₁ : A = bwd (fwd (z .fst))
Fiber = fwd x₁ ≡ y
f₁ : fwd (cong bwd (z .snd) i) ≡ y
     fwd (bwd (z .snd i)) ≡ y = surj (z .snd i) ∘ z .snd
f₂ : fwd (inj (z .fst) i) ≡ y
f₂ : fwd (inj (z .fst) i) ≡ y

but even if i connected the .fst terms I still don't know how to do
mapFibers...
-}

{-
hfill can give general proofs that u0 ≡ hcomp u u0
in hcomp u u0, u0 is a base path/cube, and u is a family of paths from u0 to
something
in mapFibers it feels like we have a base path λ i → f (p i)
and we do have z₁ .snd and z₂ .snd which come from this path out to y

oh hcomp is exactly the kind of thing i thought i needed to compose my
heterogeneous paths before, what do you know

it seems like mapFibers will require a composition, and hence i might as well
try to directly compose my paths inside fromIso, instead of composing paths to
create a p to pass to mapFibers which will then compose with this...

mapFibers would still be a nice exercise

so in our .snd .snd we have an i and a j, and we want to present a B
our four corners are
  y       y

π₁ z₁   π₁ z₂

so our paths should be pretty clear

this is... a valid hcomp expression
but what i actually want is f (p i) ≡ y
so that would be our top two corners
what about

f (p i)      f


f (π₁ z₁)  f(π z₂)

then path on left is π₂ z₁ (i ∧ j′)
path on the right is π₂ z₂
base path is f (p i′)

what is i′? j? I think so


ok that's something, but how do i actually map f (p i) to f (π₁ z₁)
f (p i) is already on the path we're using from f (π₁ z₁) to f (π₁ z₂)
so shouldnt we just use refl on the left and f (p (i ∧ j)) on the bottom
-}

