open import Mapping
open import Cayley  -- should split this into Group and Cayley

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Vec as Vec
open Vec
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

record Perm {{n : ℕ}} : Set where
  field
    image : Mapping
    preimage : Mapping
    .surj : ∀ (i : Fin n) -> (image $ preimage $ i) ≡ i
    .inj : ∀ (i : Fin n) -> (preimage $ image $ i) ≡ i

open Perm

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
  Functional.compReduce functionalPerm {snd} {fst} =
      compReduce {Mapping} {image snd} {image fst}


preimageDetermined : {{n : ℕ}} {x y : Perm} ->
    image x ≡ image y -> preimage x ≡ preimage y
preimageDetermined {{n}} {x} {y} refl = extensional proof
  where
    proof : ∀ (i : Fin n) → (preimage x $ i) ≡ (preimage y $ i)
    proof i =
        (preimage x $ i) ≡⟨ inj y ⟩
        (preimage y $ image y $ preimage x $ i)
            ≡⟨ ? ⟩
        (preimage y $ image x $ preimage x $ i)
            ≡⟨ cong (preimage y $_) (surj x) ⟩
        (preimage y $ i) ∎
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
    (∀ (i : Fin n) → (x $ i) ≡ (y $ i)) -> x ≡ y
permExtension ex = permDetermined (extensional ex)


invert : {{n : ℕ}} -> Perm -> Perm
invert x = inverse
  where
    inverse : Perm
    image inverse = preimage x
    preimage inverse = image x
    surj inverse = inj x
    inj inverse = surj x

idPerm : {{n : ℕ}} → Perm
Perm.image idPerm = id
Perm.preimage idPerm = id
Perm.surj idPerm = {! permExtension; id-prop !}
Perm.inj idPerm = ?

instance
  groupPerm : {{n : ℕ}} → Group Perm
  _≟_ {{groupPerm}} = ?
  _*_ {{groupPerm}} = _∘_
  associative {{groupPerm}} a b c = {! permExtension (funAssoc {Perm} a b c) !}
  ε {{groupPerm}} = idPerm
  left-id {{groupPerm}} a = ?
  right-id {{groupPerm}} a = ?
  _⁻¹ {{groupPerm}} = invert
  left-inverse {{groupPerm}} a = ?
  right-inverse {{groupPerm}} a = ?
