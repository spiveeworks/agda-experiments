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

_≡_ : ∀ {l r : Level} {A : Set l} -> A -> A -> Set (l ⊔ lsuc r)
_≡_ {l} {r} {A} x y = ∀ (C : A -> Set r) -> C x -> C y

refl : ∀ {l r : Level} {A : Set l} {x : A} -> _≡_ {l} {r} x x
refl {x = x} C y = y

J : ∀ {l r : Level} {A : Set l} (_~_ : A -> A -> Set r) (refl′ : ∀ x → x ~ x) -> ∀ x y → _≡_ {l} {r} x y → x ~ y
J _~_ refl′ x y p = p (x ~_) (refl′ x)



IsProp : Set -> Set₁
IsProp A = (C : A -> A -> Set) -> ((x : A) -> C x x) -> (x y : A) -> C x y

mapProp : (A B : Set) -> (f : A -> B) -> (g : B -> A) -> (∀ x → f (g x) ≡ x) → IsProp A -> IsProp B
mapProp A B f g inv base C m x y = inv y (λ y → C x y) (inv x (λ x → C x (f (g y))) out) where
  out : C (f (g x)) (f (g y))
  out = base (λ x′ y′ → C (f x′) (f y′)) (λ x′ → m (f x′)) (g x) (g y)

record InvAFunctor {la lb} (F : Set la -> Set lb) : Set (lsuc la ⊔ lb) where
  field
    {{aF}} : AFunctor F
    invF : {A B : Set la} → (f : A → B) → (g : B → A) → (∀ x → g (f x) ≡ x) →
        (∀ y → f (g y) ≡ y) → ∀ mx → mapg f g (mapf f g mx) ≡ mx

postulate
  allFunctor : ∀ {la lb} (F : Set la → Set lb) → InvAFunctor F

uv : (A B : Set) → (f : A → B) → (g : B → A) → (∀ x → g (f x) ≡ x) →
  (∀ y → f (g y) ≡ y) → A ≡ B
uv A B f g g∘f f∘g C mA = mapf {{InvAFunctor.aF (allFunctor C)}} f g mA


