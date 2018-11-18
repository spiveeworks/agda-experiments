open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Vec as Vec
open Vec
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

Mapping : {{n : ℕ}} -> Set
Mapping {{n}} = Vec (Fin n) n

fromFun : {{n : ℕ}} -> (Fin n -> Fin n) -> Mapping
fromFun {{n}} f = Vec.map f (Vec.allFin n)


extensional : {A : Set} (n : ℕ) (x y : Vec A n) ->
    (∀ (i : Fin n) -> Vec.lookup i x ≡ Vec.lookup i y) -> x ≡ y
extensional ℕ.zero [] [] _ = refl
extensional {A} (ℕ.suc n) (x ∷ xs) (y ∷ ys) eq = step eqh eqt
  where
    step : {x y : A} {xs ys : Vec A n} ->
        x ≡ y -> xs ≡ ys -> (x ∷ xs) ≡ (y ∷ ys)
    step refl refl = refl

    eqh = eq Fin.zero

    eq' : ∀ (i : Fin n) -> Vec.lookup i xs ≡ Vec.lookup i ys
    eq' i = eq (Fin.suc i)
    eqt = extensional n xs ys eq'

unextensional : {A : Set} {n : ℕ} {x y : Vec A n} ->
    x ≡ y -> ∀ (i : Fin n) -> Vec.lookup i x ≡ Vec.lookup i y
unextensional {A} {n} {x} {_} p i = PropEq.subst P p refl
  where
    P : Vec A n -> Set
    P y = Vec.lookup i x ≡ Vec.lookup i y

record Functional (MA : Set) : Set1 where
  infixr 9 _∘_
  infixr -1 _$_
  field
    A : Set
    _$_ : MA -> A -> A
    _∘_ : MA -> MA -> MA
    compReduce : ∀ {f g : MA} {x : A} -> (f ∘ g $ x) ≡ (f $ g $ x)

open Functional {{...}} hiding (A)

mapLaw : {A B : Set} {n : ℕ} (f : A -> B) (x : Vec A n) ->
    ∀ (i : Fin n) -> lookup i (map f x) ≡ f (lookup i x)
mapLaw {n = ℕ.zero} f x ()
mapLaw {n = ℕ.suc m} f (x ∷ xs) (Fin.zero) = refl
mapLaw {n = ℕ.suc m} f (x ∷ xs) (Fin.suc i) = mapLaw {n = m} f xs i

instance
  functionalMapping : {{n : ℕ}} -> Functional Mapping
  Functional.A (functionalMapping {{n}}) = Fin n
  Functional._$_ functionalMapping mapping i = lookup i mapping
  Functional._∘_ functionalMapping snd fst = Vec.map (_$_ snd) fst
  -- ((map (_$_ f) g) $ x) ≡ (f $ g $ x)
  Functional.compReduce (functionalMapping {{n}}) {f} {g} {x} =
      mapLaw (_$_ f) g x

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
