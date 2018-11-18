module Mapping where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Vec as Vec
open Vec
open import Relation.Binary.PropositionalEquality
    as PropEq using (_≡_; refl; subst; trans)

------------------------------------------------------------------------
-- Functional class, properties (motivation below)

record Functional (MA : Set) : Set1 where
  infixr 9 _∘_
  infixr -1 _$_
  field
    A : Set
    _$_ : MA -> A -> A
    _∘_ : MA -> MA -> MA
    compReduce : ∀ {f g : MA} {x : A} -> (f ∘ g $ x) ≡ (f $ g $ x)

open Functional {{...}} public hiding (A)

Item : {MA : Set} {{Fun : Functional MA}} → Set
Item {{Fun}} = Functional.A Fun

IsLeftInverse : {MA : Set} {{Fun : Functional MA}} → (f g : MA) → Set
IsLeftInverse {{Fun}} f g = ∀ (i : Item {{Fun}}) → (f $ g $ i) ≡ i

-- IsRightInverse : {MA : Set} {{Fun : Functional MA}} → (f g : MA) → Set
-- IsRightInverse f g = IsLeftInverse g f

inverseComposition : {MA : Set} {{Fun : Functional MA}}
    (x : MA) (xi : MA) (xsur : IsLeftInverse x xi)
    (y : MA) (yi : MA) (ysur : IsLeftInverse y yi)
    -> IsLeftInverse (x ∘ y) (yi ∘ xi)
inverseComposition {MA} {{Fun}} x xi xsur y yi ysur i = eq15
  where
    -- since each of these equals the previous, the first should equal the last
    Ex1 = x ∘ y $ yi ∘ xi $ i
    Ex2 = x ∘ y $ yi $ xi $ i
    Ex3 = x $ y $ yi $ xi $ i
    Ex4 = x $          xi $ i
    Ex5 =                   i

    eq12 : Ex1 ≡ Ex2
    eq12 = subst Eq12 eqex refl
      where
        Eq12 : Item {{Fun}} -> Set
        Eq12 ex = Ex1 ≡ (x ∘ y $ ex)
        eqex : (yi ∘ xi $ i) ≡ (yi $ xi $ i)
        eqex = compReduce {{Fun}} {yi} {xi} {i}
    eq23 : Ex2 ≡ Ex3
    eq23 = compReduce {{Fun}} {x} {y} {yi $ xi $ i}
    eq34 : Ex3 ≡ Ex4
    eq34 = subst Eq34 eqex refl
      where
        Eq34 : Item {{Fun}} -> Set
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


------------------------------------------------------------------------
-- Vec as function

-- think of this as the opposite of a table: interface a vec as a function

Mapping : {{n : ℕ}} -> Set
Mapping {{n}} = Vec (Fin n) n

fromFun : {{n : ℕ}} -> (Fin n -> Fin n) -> Mapping
fromFun {{n}} f = Vec.map f (Vec.allFin n)


extensional : {A : Set} {n : ℕ} {x y : Vec A n} ->
    (∀ (i : Fin n) -> Vec.lookup i x ≡ Vec.lookup i y) -> x ≡ y
extensional {A} {ℕ.zero} {[]} {[]} _ = refl
extensional {A} {ℕ.suc n} {x ∷ xs} {y ∷ ys} eq = step eqh eqt
  where
    step : {x y : A} {xs ys : Vec A n} ->
        x ≡ y -> xs ≡ ys -> (x ∷ xs) ≡ (y ∷ ys)
    step refl refl = refl

    eqh = eq Fin.zero

    eq' : ∀ (i : Fin n) -> Vec.lookup i xs ≡ Vec.lookup i ys
    eq' i = eq (Fin.suc i)
    eqt = extensional eq'

unextensional : {A : Set} {n : ℕ} {x y : Vec A n} ->
    x ≡ y -> ∀ (i : Fin n) -> Vec.lookup i x ≡ Vec.lookup i y
unextensional {A} {n} {x} {_} p i = PropEq.subst P p refl
  where
    P : Vec A n -> Set
    P y = Vec.lookup i x ≡ Vec.lookup i y


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

