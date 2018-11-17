open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Vec as Vec
open Vec using (Vec)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

Mapping : {{n : ℕ}} -> Set
Mapping {{n}} = Vec (Fin n) n

fromFun : {{n : ℕ}} -> (Fin n -> Fin n) -> Mapping
fromFun {{n}} f = Vec.map f (Vec.allFin n)

record Functional (MA : Set) : Set1 where
  infixr 9 _∘_
  infixr -1 _$_
  field
    A : Set
    _$_ : MA -> A -> A
    _∘_ : MA -> MA -> MA
    compReduce : ∀ {f g : MA} {x : A} -> (f ∘ g $ x) ≡ (f $ g $ x)

open Functional {{...}} hiding (A)

instance
  functionalMapping : {{n : ℕ}} -> Functional Mapping
  Functional.A (functionalMapping {{n}}) = Fin n
  Functional._$_ functionalMapping mapping i = Vec.lookup i mapping
  Functional._∘_ functionalMapping snd fst = Vec.map (_$_ snd) fst
  Functional.compReduce functionalMapping {snd} {fst} {x} = ?

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
