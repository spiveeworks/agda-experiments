module RelExt where

open import Agda.Primitive
open import Relation.Binary

module SymExt where
  data SymExt {A : Set} (_~_ : Rel A lzero) (x y : A) : Set where
    fwd : x ~ y → SymExt _~_ x y
    bwd : y ~ x → SymExt _~_ x y

  sym : {A : Set} → (_~_ : Rel A lzero) → Symmetric (SymExt _~_)
  sym _ (fwd r) = bwd r
  sym _ (bwd r) = fwd r

  image : {A B : Set} → (f : A → B) → (_~_ : Rel A lzero) → (_~′_ : Rel B lzero)
    → (∀ x y → x ~ y → f x ~′ f y) →
    ∀ x y → SymExt _~_ x y → SymExt _~′_ (f x) (f y)
  image f _ _ base x y (fwd p) = fwd (base x y p)
  image f _ _ base x y (bwd p) = bwd (base y x p)

module TransExt where
  data TransExt {A : Set} (_~_ : Rel A lzero) (x : A) : A → Set where
    refl : TransExt _~_ x x
    -- excuse the reversed convention vs list, keeps x out the front
    cons : {y z : A} → TransExt _~_ x y → y ~ z → TransExt _~_ x z

  trans : {A : Set} → (_~_ : Rel A lzero) → Transitive (TransExt _~_)
  trans _ xz refl = xz
  trans _ xy (cons yw wz) = cons (trans _ xy yw) wz

  symHelper : {A : Set} (_~_ : Rel A lzero) → Symmetric _~_ →
    ∀ {x y z} → TransExt _~_ x y → TransExt _~_ z y → TransExt _~_ z x
  symHelper _ base refl zx = zx
  symHelper _ base (cons xw wy) zy = symHelper _ base xw (cons zy (base wy))

  sym : {A : Set} → (_~_ : Rel A lzero) → Symmetric _~_ → Symmetric (TransExt _~_)
  sym _ base p = symHelper _ base p refl

  image : {A B : Set} → (f : A → B) → (_~_ : Rel A lzero) → (_~′_ : Rel B lzero)
    → (∀ x y → x ~ y → f x ~′ f y) →
    ∀ x y → TransExt _~_ x y → TransExt _~′_ (f x) (f y)
  image f _ _ base _ _ refl = refl
  image f _ _ base x z (cons xy yz) =
    cons (image f _ _ base x _ xy) (base _ z yz)

module EquivExt where
  open TransExt using (TransExt)
  open SymExt using (SymExt)

  EquivExt : {A : Set} → Rel A lzero → Rel A lzero
  EquivExt _~_ = TransExt (SymExt _~_)

  refl : {A : Set} → (_~_ : Rel A lzero) → Reflexive (EquivExt _~_)
  refl _~_ = TransExt.refl

  sym : {A : Set} → (_~_ : Rel A lzero) → Symmetric (EquivExt _~_)
  sym _~_ = TransExt.sym (SymExt _~_) (SymExt.sym _~_)

  trans : {A : Set} → (_~_ : Rel A lzero) → Transitive (EquivExt _~_)
  trans _~_ = TransExt.trans (SymExt _~_)

  image : {A B : Set} → (f : A → B) → (_~_ : Rel A lzero) → (_~′_ : Rel B lzero)
    → (∀ x y → x ~ y → f x ~′ f y) →
    ∀ x y → EquivExt _~_ x y → EquivExt _~′_ (f x) (f y)
  image f _~_ _~′_ base = TransExt.image f (SymExt _~_) (SymExt _~′_)
    (SymExt.image f _~_ _~′_ base)

module RelImage where
  import Relation.Binary.PropositionalEquality as PropEq

  data RelImage {F A B : Set} (_$_ : F → A → B) (_~_ : Rel A lzero) : Rel B lzero where
    image : ∀ f {x y} → x ~ y → RelImage _$_ _~_ (f $ x) (f $ y)

  rel-transp : ∀ {A : Set} {x₁ y₁ x₂ y₂ : A} (_~_ : Rel A lzero) →
    x₁ PropEq.≡ x₂ → y₁ PropEq.≡ y₂ → x₁ ~ y₁ → x₂ ~ y₂
  rel-transp _ PropEq.refl PropEq.refl p = p

  cong : {F A : Set} (_~_ : Rel A lzero) (_$_ : F → A → A) (_∘_ : F → F → F) →
    (compprop : ∀ f g x → (f ∘ g) $ x PropEq.≡ f $ (g $ x)) →
    ∀ f x y → RelImage _$_ _~_ x y → RelImage _$_ _~_ (f $ x) (f $ y)
  cong _~_ _$_ _∘_ compprop f _ _ (image g {x} {y} p) =
    rel-transp (RelImage _$_ _~_)
      (compprop f g x) (compprop f g y)
      (image (f ∘ g) p)

  sym : {F A B : Set} (_$_ : F → A → B) (_~_ : Rel A lzero) →
    Symmetric _~_ → Symmetric (RelImage _$_ _~_)
  sym _ _ base (image f p) = image f (base p)

