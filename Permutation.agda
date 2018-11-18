open import Mapping

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Vec as Vec
open Vec
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

record Perm {{n : ℕ}} : Set where
  field
    image : Mapping
    preimage : Mapping
    .surj : ∀ (i : Fin n) -> (image $ preimage $ i) ≡ i
    .inj : ∀ (i : Fin n) -> (preimage $ image $ i) ≡ i

open Perm

permDetermined : {{n : ℕ}} {x y : Perm} ->
    image x ≡ image y -> preimage x ≡ preimage y
permDetermined {x} {y} refl = extensional _ _ _ ?
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

instance
  functionalPerm : {{n : ℕ}} -> Functional Perm
  Functional.A (functionalPerm {{n}}) = Fin n
  Functional._$_ functionalPerm perm i = image perm $ i
  Functional._∘_ functionalPerm snd fst = result
    where
      result : Perm
      image result = image snd ∘ image fst
      preimage result = preimage fst ∘ preimage snd
      surj result i = ?
      inj result i = ?
  Functional.compReduce functionalPerm {snd} {fst} {x} = ?

invert : {{n : ℕ}} -> Perm -> Perm
invert x = inverse
  where
    inverse : Perm
    image inverse = preimage x
    preimage inverse = image x
    surj inverse = inj x
    inj inverse = surj x


-- _∘_ : {{n : ℕ}} -> Perm -> Perm -> Perm
-- x ∘ y = 
