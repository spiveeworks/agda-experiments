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

module Closures {b} {a} {A : Set a} (_#_ : Rel {b} A) where
  data SymClosure (x y : A) : Set b where
    base : x # y → SymClosure x y
    sym : y # x → SymClosure x y

  symclosure-sym : Symmetric SymClosure
  symclosure-sym (base p) = sym p
  symclosure-sym (sym p) = base p

  symclosureproof : ∀ {b′} → SymClosure ⇒ RelClosure {b} {b′} Symmetric _#_
  symclosureproof (base p) _~_ imp symprf = imp p
  symclosureproof (sym p) _~_ imp symprf = symprf (imp p)

  symclosureequiv : SymClosure ⇔ RelClosure {b} {b} Symmetric _#_
  _⇔_.fwd symclosureequiv = symclosureproof
  _⇔_.bwd symclosureequiv cls = cls SymClosure SymClosure.base symclosure-sym

  data TransClosure (x y : A) : Set (a ⊔ b) where
    base : x # y → TransClosure x y
    cons : ∀ {x′} → TransClosure x x′ → x′ # y → TransClosure x y

  transclosure-trans : Transitive TransClosure
  transclosure-trans p₁ (base p₂) = cons p₁ p₂
  transclosure-trans p₁ (cons p₂ p₃) = cons (transclosure-trans p₁ p₂) p₃

  transclosureproof : ∀ {b′} → TransClosure ⇒ RelClosure {b} {b′} Transitive _#_
  transclosureproof (base p) _<_ imp transprf = imp p
  transclosureproof (cons p₁ p₂) _<_ imp transprf = transprf
    (transclosureproof p₁ _<_ imp transprf)
    (imp p₂)

  transclosureequiv : TransClosure ⇔ RelClosure {b} {a ⊔ b} Transitive _#_
  _⇔_.fwd transclosureequiv = transclosureproof
  _⇔_.bwd transclosureequiv cls = cls TransClosure TransClosure.base transclosure-trans

  data PreorderClosure : Rel {a ⊔ b} A where
    refl : ∀ {x} → PreorderClosure x x
    cons : ∀ {x} {y} {z} → PreorderClosure x y → y # z → PreorderClosure x z

  preorderclosure-embed : _#_ ⇒ PreorderClosure
  preorderclosure-embed p = cons refl p

  preorderclosure-trans : Transitive PreorderClosure
  preorderclosure-trans p₁ refl = p₁
  preorderclosure-trans p₁ (cons p₂ p₃) = cons (preorderclosure-trans p₁ p₂) p₃

  preorderclosure-ispre : IsPreorder PreorderClosure
  preorderclosure-ispre = record{refl = PreorderClosure.refl; trans = preorderclosure-trans}

  preorderclosureproof : ∀ {b′} → PreorderClosure ⇒ RelClosure {b} {b′} IsPreorder _#_
  preorderclosureproof refl _<_ imp ispre = IsPreorder.refl ispre
  preorderclosureproof (cons p₁ p₂) _<_ imp ispre = IsPreorder.trans ispre
    (preorderclosureproof p₁ _<_ imp ispre)
    (imp p₂)

  preorderclosureequiv : PreorderClosure ⇔ RelClosure {b} {a ⊔ b} IsPreorder _#_
  _⇔_.fwd preorderclosureequiv = preorderclosureproof
  _⇔_.bwd preorderclosureequiv cls = cls PreorderClosure preorderclosure-embed preorderclosure-ispre
