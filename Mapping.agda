{-# OPTIONS --allow-unsolved-metas #-}
module Mapping where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Vec as Vec
open Vec
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

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

funAssoc : {MA : Set} {{Fun : Functional MA}} → (f g h : MA) →
    ∀ (i : Item {{Fun}}) → ((f ∘ g) ∘ h $ i) ≡ (f ∘ (g ∘ h) $ i)
funAssoc f g h i = ?
{-# WARNING_ON_USAGE funAssoc "remember to disable allow-unsolved-metas!" #-}

-- IsRightInverse : {MA : Set} {{Fun : Functional MA}} → (f g : MA) → Set
-- IsRightInverse f g = IsLeftInverse g f

inverseComposition : {MA : Set} {{Fun : Functional MA}}
    (x : MA) (xi : MA) (xsur : IsLeftInverse x xi)
    (y : MA) (yi : MA) (ysur : IsLeftInverse y yi)
    -> IsLeftInverse (x ∘ y) (yi ∘ xi)
inverseComposition {MA} {{Fun}} x xi xsur y yi ysur i =
    (x ∘ y $ yi ∘ xi $ i) ≡⟨ cong (λ ex → x ∘ y $ ex) (compReduce′ i) ⟩
    (x ∘ y $ yi $ xi $ i) ≡⟨ compReduce′ (yi $ xi $ i) ⟩
    (x $ y $ yi $ xi $ i) ≡⟨ cong (x $_) (ysur (xi $ i)) ⟩
    (x $          xi $ i) ≡⟨ xsur i ⟩
    (                  i) ∎
  where
    compReduce′ : {x y : MA} (i : Item {{Fun}}) → (x ∘ y $ i) ≡ (x $ y $ i)
    compReduce′ {x} {y} i = compReduce {{Fun}} {x} {y} {i}


------------------------------------------------------------------------
-- Vec as function

-- think of this as the opposite of a table: interface a vec as a function

Mapping : {{n : ℕ}} -> Set
Mapping {{n}} = Vec (Fin n) n

-- generalize to functor
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

-- functor + functional + ident -> id {MA} = fmap f (id {A->A})
-- btw _∘_ = λ f → fmap (f +_)
fromFun : {{n : ℕ}} -> (Fin n -> Fin n) -> Mapping
fromFun {{n}} f = Vec.map f (Vec.allFin n)

id : {{n : ℕ}} -> Mapping
id {{n}} = Vec.allFin n

-- we're basically instantiating a monoid
-- I'll probably switch to std one day??
id-prop : {{n : ℕ}} → ∀ (i : Fin n) → (id $ i) ≡ i
id-prop {{ℕ.zero}} ()
id-prop {{ℕ.suc n}} Fin.zero = refl
id-prop {{ℕ.suc n}} (Fin.suc i) = ?

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
unextensional {A} {n} {x} {_} p i = cong (Vec.lookup i) p

