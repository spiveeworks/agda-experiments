open import Agda.Primitive
open import Function using (_∘_)


List : (A : Set) -> Set₁
List A = {C : Set} -> (A -> C -> C) -> C -> C
empty : {A : Set} -> List A
empty f acc = acc
cons : {A : Set} -> A -> List A -> List A
cons x xs f acc = f x (xs f acc)

map₁ : (A B : Set) -> (g : B -> A) -> (C : Set) ->
  (A -> C -> C) -> (B -> C -> C)
map₁ A B g C base y acc = base (g y) acc

map₂ : (A B : Set) -> (f : A -> B) ->
  ({C : Set} -> (A -> C -> C) -> C -> C) ->
  ({C : Set} -> (B -> C -> C) -> C -> C)
map₂ A B f base fun acc = base (λ x acc′ -> fun (f x) acc′) acc

fmap : (A B : Set) -> (f : A -> B) -> List A -> List B
fmap = map₂


record AFunctor {la lb} (F : Set la -> Set lb) : Set (lsuc la ⊔ lb) where
  field
    mapf : {A B : Set la} -> (f : A -> B) -> (g : B -> A) -> F A -> F B
  mapg : {A B : Set la} -> (f : A -> B) -> (g : B -> A) -> F B -> F A
  mapg f g = mapf g f

open AFunctor {{...}} public

buildFunctorExp : ∀ {la lb} -> (F₁ F₂ : Set la -> Set lb) ->
  AFunctor F₁ -> AFunctor F₂ -> AFunctor (λ A -> F₁ A -> F₂ A)
buildFunctorExp {la} F₁ F₂ aF₁ aF₂ = record {mapf = out} where
  out : {A B : Set la} -> (f : A -> B) -> (g : B -> A) ->
    (F₁ A -> F₂ A) -> (F₁ B -> F₂ B)
  out f g base = mapf {{aF₂}} f g ∘ base ∘ mapg {{aF₁}} f g

-- identity type based on transportation between type constructors
TId : ∀ {l r : Level} {A : Set l} -> A -> A -> Set (l ⊔ lsuc r)
TId {l} {r} {A} x y = ∀ (C : A -> Set r) -> C x -> C y

reflTrans : ∀ {l r : Level} {A : Set l} {x : A} -> TId {l} {r} x x
reflTrans {x = x} C y = y

JTrans : ∀ {l r : Level} {A : Set l} (_~_ : A -> A -> Set r) (refl′ : ∀ x → x ~ x) -> ∀ x y → TId {l} {r} x y → x ~ y
JTrans _~_ refl′ x y p = p (x ~_) (refl′ x)



IsProp : Set -> Set₁
IsProp A = (C : A -> A -> Set) -> ((x : A) -> C x x) -> (x y : A) -> C x y

mapProp : (A B : Set) -> (f : A -> B) -> (g : B -> A) -> (∀ x → TId (f (g x)) x) → IsProp A -> IsProp B
mapProp A B f g inv base C m x y = inv y (λ y → C x y) (inv x (λ x → C x (f (g y))) out) where
  out : C (f (g x)) (f (g y))
  out = base (λ x′ y′ → C (f x′) (f y′)) (λ x′ → m (f x′)) (g x) (g y)


data _≡_ {l} {A : Set l} : A → A → Set l where
  refl : (x : A) → x ≡ x

JId : ∀ {l r} {A : Set l} → A → A → Set (l ⊔ lsuc r)
JId {l} {r} {A} x y = (_~_ : A → A → Set r) → (z : ∀ x → x ~ x) → x ~ y

fromJId : ∀ {l} {A : Set l} → (x y : A) → JId {l} {l} x y → x ≡ y
fromJId x y p = p _≡_ refl

toJId : ∀ {l} {r} {A : Set l} → (x y : A) → x ≡ y → JId {l} {r} x y
toJId _ _ (refl x) _ refl′ = refl′ x

record _↔_ {l} (A B : Set l) : Set l where
  field
    isoFwd : A → B
    isoBwd : B → A
    isoSurj : (y : B) → isoFwd (isoBwd y) ≡ y
    isoInj : (x : A) → isoBwd (isoFwd x) ≡ x

open _↔_ public

isoRefl : ∀ {l} (A : Set l) → A ↔ A
isoFwd (isoRefl A) x = x
isoBwd (isoRefl A) x = x
isoSurj (isoRefl A) = refl
isoInj (isoRefl A) = refl

isoInv : ∀ {l} {A B : Set l} → A ↔ B → B ↔ A
isoInv iso .isoFwd = iso .isoBwd
isoInv iso .isoBwd = iso .isoFwd
isoInv iso .isoSurj = iso .isoInj
isoInv iso .isoInj = iso .isoSurj

IsoFunctor : ∀ {la lb} (F : Set la → Set lb) → Set (lsuc la ⊔ lb)
IsoFunctor {la} F = (A B : Set la) → A ↔ B → F A ↔ F B

postulate
  allFunctor : ∀ {la lb} (F : Set la → Set lb) → IsoFunctor F

uv : (A B : Set) → A ↔ B → A ≡ B
uv A B iso = allFunctor (A ≡_) A B iso .isoFwd (refl A)

uvJ : ∀ {l} {r} (A B : Set l) → A ↔ B → JId {lsuc l} {r} A B
uvJ A B iso _~_ m = allFunctor (A ~_) A B iso .isoFwd (m A)

{-
isoJId : ∀ {l} (A : Set l) → IsoFunctor (JId A)
isoJId A B₁ B₂ iso .isoFwd eq₁ _~_ m = allFunctor (A ~_) B₁ B₂ iso .isoFwd (eq₁ _~_ m)
isoJId A B₁ B₂ iso .isoBwd eq₂ _~_ m = allFunctor (A ~_) B₁ B₂ iso .isoBwd (eq₂ _~_ m)
isoJId A B₁ B₂ iso .isoSurj eq₂ = allFunctor (A ~_) B₁ B₂ iso .isoSurj (eq₁ _~_ m)
isoJId A B₁ B₂ iso .isoInj eq₁ = allFunctor (A ~_) B₁ B₂ iso .isoInj (eq₁ _~_ m)
-}

-- copy pasted from agda stdlib
_≡⟨_⟩_ : ∀ {l} → {A : Set l} → (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ refl _ ⟩ refl _ = refl _

_≡˘⟨_⟩_ : ∀ {l} → {A : Set l} (x {y z} : A) → y ≡ x → y ≡ z → x ≡ z
_ ≡˘⟨ refl _ ⟩ refl _ = refl _

_∎ : ∀ {l} → {A : Set l} (x : A) → x ≡ x
_∎ _ = refl _

isoExp : ∀ {l r} (F₁ F₂ : Set l → Set r) → IsoFunctor F₁ → IsoFunctor F₂ → IsoFunctor (λ A → F₁ A → F₂ A)
isoExp F₁ F₂ isoF₁ isoF₂ A B iso = out where
  iso₁ = isoF₁ A B iso
  iso₂ = isoF₂ A B iso
  out : (F₁ A → F₂ A) ↔ (F₁ B → F₂ B)
  out .isoFwd base = iso₂ .isoFwd ∘ base ∘ iso₁ .isoBwd
  out .isoBwd base = iso₂ .isoBwd ∘ base ∘ iso₁ .isoFwd
  out .isoSurj y = ? -- function extensionality/composition inversion needed
  out .isoInj y = ?


