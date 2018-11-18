open import Mapping

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Vec as Vec
open Vec
open import Relation.Binary.PropositionalEquality

record Perm {{n : ℕ}} : Set where
  field
    image : Mapping
    preimage : Mapping
    .surj : ∀ (i : Fin n) -> (image $ preimage $ i) ≡ i
    .inj : ∀ (i : Fin n) -> (preimage $ image $ i) ≡ i

open Perm

{-
preimageDetermined : {{n : ℕ}} {x y : Perm} ->
    image x ≡ image y -> preimage x ≡ preimage y
preimageDetermined {x} {y} refl = extensional ?
{-
x.surj : x.image $ x.preimage $ i = i
but x.image = y.image so
y.image $ x.preimage $ i = i
apply (y.preimage $_) to both sides
y.preimage $ y.image $ x.preimage $ i = y.preimage $ i
apply y.surj to x.preimage $ i
y.preimage $ y.image $ x.preimage $ i = x.preimage $ i
therefore x.preimage $ i = y.preimage $ i (transitivity)

by choosing the intermediate steps carefully you could do this without relying
on symmetry arguments

not sure what this argument looks like with refl pattern matching
-}

permEq : {{n : ℕ}} {x y : Perm} ->
    image x ≡ image y -> preimage x ≡ preimage y -> x ≡ y
permEq refl refl = refl

permDetermined : {{n : ℕ}} {x y : Perm} ->
    image x ≡ image y -> x ≡ y
permDetermined p = permEq p (preimageDetermined p)

permExtension : {{n : ℕ}} {x y : Perm} ->
    (∀ (i : Fin n) → (image x $ i) ≡ (image y $ i)) -> x ≡ y
permExtension ex = permDetermined (extensional ex)
-}

inverseComposition : {{n : ℕ}} {A : Set}
    (x : Mapping) (xi : Mapping) (xsur : ∀ (i : Fin n) → (x $ xi $ i) ≡ i)
    (y : Mapping) (yi : Mapping) (ysur : ∀ (i : Fin n) → (y $ yi $ i) ≡ i)
    -> ∀ (i : Fin n) → ((x ∘ y) $ (yi ∘ xi) $ i) ≡ i
inverseComposition {{n}} x xi xsur y yi ysur i = eq15
  where
    Ex1 = x ∘ y $ yi ∘ xi $ i
    Ex2 = x ∘ y $ yi $ xi $ i
    Ex3 = x $ y $ yi $ xi $ i
    Ex4 = x $          xi $ i
    Ex5 =                   i

    eq12 : Ex1 ≡ Ex2
    eq12 = subst Eq12 eqex refl
      where
        Eq12 : Fin n -> Set
        Eq12 ex = Ex1 ≡ (x ∘ y $ ex)
        eqex : (yi ∘ xi $ i) ≡ (yi $ xi $ i)
        eqex = compReduce {Mapping} {yi} {xi} {i}
    eq23 : Ex2 ≡ Ex3
    eq23 = compReduce {Mapping} {x} {y} {yi $ xi $ i}
    eq34 : Ex3 ≡ Ex4
    eq34 = subst Eq34 eqex refl
      where
        Eq34 : Fin n -> Set
        Eq34 ex = Ex3 ≡ (x $ ex)
        eqex : (y $ yi $ xi $ i) ≡ (xi $ i)
        eqex = ysur (xi $ i)
    eq45 : Ex4 ≡ Ex5
    eq45 = xsur i

    eq13 : Ex1 ≡ Ex3
    eq13 = trans eq12 eq23
    eq14 : Ex1 ≡ Ex4
    eq14 = trans eq13 eq34
    eq15 : Ex1 ≡ Ex5
    eq15 = trans eq14 eq45

instance
  functionalPerm : {{n : ℕ}} -> Functional Perm
  Functional.A (functionalPerm {{n}}) = Fin n
  Functional._$_ functionalPerm perm i = image perm $ i
  Functional._∘_ functionalPerm x y = result
    where
      result : Perm
      image result = image x ∘ image y
      preimage result = preimage y ∘ preimage x
      surj result = inverseComposition
          (image x) (preimage x) (surj x)
          (image y) (preimage y) (surj y)
      inj result = inverseComposition
          (preimage y) (image y) (inj y)
          (preimage x) (image x) (inj x)
  Functional.compReduce functionalPerm {snd} {fst} {i} =
      compReduce {Mapping} {image snd} {image fst} {i}

invert : {{n : ℕ}} -> Perm -> Perm
invert x = inverse
  where
    inverse : Perm
    image inverse = preimage x
    preimage inverse = image x
    surj inverse = inj x
    inj inverse = surj x

