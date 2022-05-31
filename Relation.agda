open import Agda.Primitive

Rel : ∀ {b} {a} → Set a → Set (a ⊔ lsuc b)
Rel {b} A = A → A → Set b

_⇒_ : ∀ {b₁} {b₂} {a} {A : Set a}
  → Rel {b₁} A → Rel {b₂} A → Set (a ⊔ b₁ ⊔ b₂)
_~_ ⇒ _#_ = ∀ {x} {y} → x ~ y → x # y

record _⇔_ {b₁} {b₂} {a} {A : Set a} (_~_ : Rel {b₁} A) (_#_ : Rel {b₂} A) : Set (a ⊔ b₁ ⊔ b₂) where
  field
    fwd : _~_ ⇒ _#_
    bwd : _#_ ⇒ _~_

RelProp : ∀ {b} {c} {a} → Set a → Set (a ⊔ lsuc b ⊔ lsuc c)
RelProp {b} {c} A = Rel {b} A → Set c

RelClosure : ∀ {b₁} {b₂} {c} {a} → {A : Set a} → RelProp {b₂} {c} A
  → Rel {b₁} A → Rel {a ⊔ b₁ ⊔ lsuc b₂ ⊔ c} A
RelClosure P _#_ x y = ∀ _~_ → (_#_ ⇒ _~_) → P _~_ → x ~ y

Reflexive : ∀ {b} {a} {A : Set a} → RelProp {b} {a ⊔ b} A
Reflexive _~_ = ∀ {x} → x ~ x

Symmetric : ∀ {b} {a} {A : Set a} → RelProp {b} {a ⊔ b} A
Symmetric _~_ = ∀ {x} {y} → x ~ y → y ~ x

Transitive : ∀ {b} {a} {A : Set a} → RelProp {b} {a ⊔ b} A
Transitive _<_ = ∀ {x} {y} {z} → x < y → y < z → x < z

record IsPreorder {b} {a} {A : Set a} (_≤_ : Rel {b} A) : Set (a ⊔ b) where
  field
    refl : Reflexive _≤_
    trans : Transitive _≤_

data SymClosure {b} {a} {A : Set a} (_#_ : Rel {b} A) (x y : A) : Set b where
  base : x # y → SymClosure _#_ x y
  sym : y # x → SymClosure _#_ x y

symclosure-sym : ∀ {b} {a} {A : Set a} (_#_ : Rel {b} A) → Symmetric (SymClosure _#_)
symclosure-sym _#_ (base p) = sym p
symclosure-sym _#_ (sym p) = base p

symclosureproof : ∀ {b₁} {b₂} {a} {A : Set a} (_#_ : Rel {b₁} A)
  → SymClosure {b₁} _#_ ⇒ RelClosure {b₁} {b₂} Symmetric _#_
symclosureproof _#_ (base p) _~_ imp symprf = imp p
symclosureproof _#_ (sym p) _~_ imp symprf = symprf (imp p)

symclosureequiv : ∀ {b} {a} {A : Set a} (_#_ : Rel {b} A)
  → SymClosure {b} _#_ ⇔ RelClosure {b} {b} Symmetric _#_
_⇔_.fwd (symclosureequiv _#_) = symclosureproof _#_
_⇔_.bwd (symclosureequiv _#_) cls = cls (SymClosure _#_)
  SymClosure.base
  (symclosure-sym _#_)

data TransClosure {b} {a} {A : Set a} (_#_ : Rel {b} A) (x y : A) : Set (a ⊔ b) where
  base : x # y → TransClosure _#_ x y
  cons : ∀ {x′} → TransClosure _#_ x x′ → x′ # y → TransClosure _#_ x y

transclosure-trans : ∀ {b} {a} {A : Set a} (_#_ : Rel {b} A) → Transitive (TransClosure _#_)
transclosure-trans _#_ p₁ (base p₂) = cons p₁ p₂
transclosure-trans _#_ p₁ (cons p₂ p₃) = cons (transclosure-trans _#_ p₁ p₂) p₃

transclosureproof : ∀ {b₁} {b₂} {a} {A : Set a} (_#_ : Rel {b₁} A)
  → TransClosure {b₁} _#_ ⇒ RelClosure {b₁} {b₂} Transitive _#_
transclosureproof _#_ (base p) _<_ imp transprf = imp p
transclosureproof _#_ (cons p₁ p₂) _<_ imp transprf = transprf
  (transclosureproof _#_ p₁ _<_ imp transprf)
  (imp p₂)

transclosureequiv : ∀ {b} {a} {A : Set a} (_#_ : Rel {b} A)
  → TransClosure {b} _#_ ⇔ RelClosure {b} {a ⊔ b} Transitive _#_
_⇔_.fwd (transclosureequiv _#_) = transclosureproof _#_
_⇔_.bwd (transclosureequiv _#_) cls = cls (TransClosure _#_)
  TransClosure.base
  (transclosure-trans _#_)

data PreorderClosure {b} {a} {A : Set a} (_#_ : Rel {b} A) : Rel {a ⊔ b} A where
  refl : ∀ {x} → PreorderClosure _#_ x x
  cons : ∀ {x} {y} {z} → PreorderClosure _#_ x y → y # z → PreorderClosure _#_ x z

preorderclosure-embed : ∀ {b} {a} {A : Set a} (_#_ : Rel {b} A) → _#_ ⇒ PreorderClosure _#_
preorderclosure-embed _#_ p = cons refl p

preorderclosure-trans : ∀ {b} {a} {A : Set a} (_#_ : Rel {b} A) → Transitive (PreorderClosure _#_)
preorderclosure-trans _#_ p₁ refl = p₁
preorderclosure-trans _#_ p₁ (cons p₂ p₃) = cons (preorderclosure-trans _#_ p₁ p₂) p₃

preorderclosure-ispre : ∀ {b} {a} {A : Set a} (_#_ : Rel {b} A) → IsPreorder (PreorderClosure _#_)
preorderclosure-ispre _#_ = record{
  refl = PreorderClosure.refl;
  trans = preorderclosure-trans _#_}

preorderclosureproof : ∀ {b₁} {b₂} {a} {A : Set a} (_#_ : Rel {b₁} A)
  → PreorderClosure {b₁} _#_ ⇒ RelClosure {b₁} {b₂} IsPreorder _#_
preorderclosureproof _#_ refl _<_ imp ispre = IsPreorder.refl ispre
preorderclosureproof _#_ (cons p₁ p₂) _<_ imp ispre = IsPreorder.trans ispre
  (preorderclosureproof _#_ p₁ _<_ imp ispre)
  (imp p₂)

preorderclosureequiv : ∀ {b} {a} {A : Set a} (_#_ : Rel {b} A)
  → PreorderClosure {b} _#_ ⇔ RelClosure {b} {a ⊔ b} IsPreorder _#_
_⇔_.fwd (preorderclosureequiv _#_) = preorderclosureproof _#_
_⇔_.bwd (preorderclosureequiv _#_) cls = cls (PreorderClosure _#_)
  (preorderclosure-embed _#_)
  (preorderclosure-ispre _#_)

