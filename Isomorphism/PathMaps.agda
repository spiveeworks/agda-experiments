-- In TypeFamilies.agda we tried to implement cong recursively, but we ended up
-- needing to define cong and transport and pi-cong redundantly at 3 different
-- arities, and it still wasn't clear how to use that to transport paths in
-- and in general it seemed like an uphill battle trying to get functions to
-- and from extensional form... So maybe we should try making heterogeneous
-- equality primary, and/or make heterogeneous function extentionality primary.

-- First, let's define transp and cong without J, since our current approach is
-- still to build J out of simpler operations that we can compute on paths.

infix 4 _≡_

data _≡_ {l} {A : Set l} (x : A) : A → Set₀ where
  refl : x ≡ x

transp : ∀ {l₁} {A B : Set l₁} → A ≡ B → A → B
transp refl x = x

cong : ∀ {l₁} {l₂} {A : Set l₁} {B : Set l₂} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong {x = x} f refl = refl

ctransp : ∀ {l₁} {l₂} {A : Set l₁} (B : (x : A) → Set l₂)
  → {x₁ x₂ : A} → x₁ ≡ x₂ → B x₁ → B x₂
ctransp B {x₁} {x₂} p = transp (cong B p)

trans : ∀ {l} {A : Set l} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans xeqy refl = xeqy

sym : ∀ {l} {A : Set l} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Next, let's define heterogeneous equality, making sure to make the
-- homogeneous path between types explicit.

data Heq {l} {A : Set l} : {B : Set l} → (A ≡ B) → A → B → Set l where
   refl : {x : A} → Heq refl x x

-- Let's play with it a little, just to get a sense of how it compares to
-- homogeneous equality, and equations like `transp p x ≡ y`

heq-transp : ∀ {l₁} → {A B : Set l₁} → {x : A} → {y : B} → (pt : A ≡ B)
  → (px : Heq pt x y) → transp pt x ≡ y
heq-transp refl refl = refl

transp-heq : ∀ {l₁} → {A B : Set l₁} → (p : A ≡ B)
  → (x : A) → Heq p x (transp p x)
transp-heq refl _ = refl

-- And define some combinators, that let us decompose cong operations into
-- builtins that we might be able to implement.

htrans : ∀ {l₁} {A B C : Set l₁} {x : A} {y : B} {z : C}
  → (p₁ : A ≡ B) → (p₂ : B ≡ C)
  → Heq p₁ x y → Heq p₂ y z → Heq (trans p₁ p₂) x z
htrans p₁ refl q₁ refl = q₁

-- Now let's actually define path maps.

Pathmap : ∀ {l₁} {l₂} {A₁ A₂ : Set l₁} (pa : A₁ ≡ A₂) {B₁ B₂ : Set l₂}
  → (pb : B₁ ≡ B₂)
  → (A₁ → B₁) → (A₂ → B₂) → Set _
Pathmap pa {B₁} {B₂} pb f₁ f₂
  = ∀ {x₁} {x₂} → (px : Heq pa x₁ x₂) → Heq pb (f₁ x₁) (f₂ x₂)

HPathmap : ∀ {l₁} {l₂} {A₁ A₂ : Set l₁} (pa : A₁ ≡ A₂)
  → {B : Set l₂}
  → (A₁ → B) → (A₂ → B) → Set l₁
HPathmap pa f₁ f₂ = ∀ {x₁} {x₂} → (px : Heq pa x₁ x₂) → f₁ x₁ ≡ f₂ x₂

DPathmap : ∀ {l₁} {l₂} {A₁ A₂ : Set l₁} (pa : A₁ ≡ A₂) (B₁ : A₁ → Set l₂) (B₂ : A₂ → Set l₂)
  → (pb : ∀ {x₁} {x₂} → Heq pa x₁ x₂ → B₁ x₁ ≡ B₂ x₂)
  → ((x : A₁) → B₁ x) → ((x : A₂) → B₂ x) → Set _
DPathmap {A₁ = A₁} {A₂} pa B₁ B₂ pb f₁ f₂
  = ∀ {x₁} {x₂} → (px : Heq pa x₁ x₂) → Heq (pb px) (f₁ x₁) (f₂ x₂)

pathmap-special-case : ∀ {l₁} {l₂} {A₁ A₂ : Set l₁} (pa : A₁ ≡ A₂) {B₁ B₂ : Set l₂}
  → (pb : B₁ ≡ B₂)
  → (f₁ : A₁ → B₁) → (f₂ : A₂ → B₂)
  → DPathmap pa (λ x → B₁) (λ x → B₂) (λ {_} {_} _ → pb) f₁ f₂ ≡ Pathmap pa pb f₁ f₂
pathmap-special-case _ _ _ _ = refl

const-pathmap : ∀ {l₁} {l₂} {A₁ A₂ : Set l₁} (pa : A₁ ≡ A₂) {B₁ B₂ : Set l₂}
  → (pb : B₁ ≡ B₂)
  → (y₁ : B₁) (y₂ : B₂) → Heq pb y₁ y₂
  → Pathmap pa pb (λ _ → y₁) (λ _ → y₂)
const-pathmap pa pb y₁ y₂ py px = py

id-pathmap : ∀ {l₁} {A₁ A₂ : Set l₁} (pa : A₁ ≡ A₂)
  → Pathmap pa pa (λ x₁ → x₁) (λ x₂ → x₂)
id-pathmap pa px = px

HPathmap₂ : ∀ {l₁} {l₂} {l₃}
  → {A₁ A₂ : Set l₁} (pa : A₁ ≡ A₂)
  → (B₁ : A₁ → Set l₂) (B₂ : A₂ → Set l₂) → (pb : HPathmap pa B₁ B₂)
  → {C : Set l₃}
  → ((x : A₁) → B₁ x → C) → ((x : A₂) → B₂ x → C) → Set _
HPathmap₂ pa B₁ B₂ pb f₁ f₂
  = ∀ {x₁} {x₂} (px : Heq pa x₁ x₂) → HPathmap (pb px) (f₁ x₁) (f₂ x₂)

DPathmap₂ : ∀ {l₁} {l₂} {l₃}
  → {A₁ A₂ : Set l₁} (pa : A₁ ≡ A₂)
  → (B₁ : A₁ → Set l₂) (B₂ : A₂ → Set l₂) → (pb : HPathmap pa B₁ B₂)
  → (C₁ : (x₁ : A₁) → B₁ x₁ → Set l₃) (C₂ : (x₂ : A₂) → B₂ x₂ → Set l₃)
  → (pc : ∀ {x₁} {x₂} (px : Heq pa x₁ x₂) → {y₁ : B₁ x₁} {y₂ : B₂ x₂} → Heq (pb px) y₁ y₂ → C₁ x₁ y₁ ≡ C₂ x₂ y₂)
  → ((x : A₁) → (y : B₁ x) → C₁ x y)
  → ((x : A₂) → (y : B₂ x) → C₂ x y)
  → Set _
DPathmap₂ {A₁ = A₁} {A₂} pa B₁ B₂ pb C₁ C₂ pc f₁ f₂
  = ∀ {x₁} {x₂} → (px : Heq pa x₁ x₂) → DPathmap (pb px) (C₁ x₁) (C₂ x₂) (pc px) (f₁ x₁) (f₂ x₂)

_∘_ : ∀ {l₁} {l₂} {l₃} {A : Set l₁} {B : A → Set l₂} {C : (x : A) → B x → Set l₃}
  → ((x : A) → (y : B x) → C x y) → (f : (x : A) → B x) → (x : A) → C x (f x)
g ∘ f = λ x → g x (f x)

compose-hpathmaps : ∀ {l₁} {l₂} {l₃} {A₁ A₂ : Set l₁} {pa : A₁ ≡ A₂}
  → {B₁ : A₁ → Set l₂} {B₂ : A₂ → Set l₂} {pb : ∀ {x₁} {x₂} → Heq pa x₁ x₂ → B₁ x₁ ≡ B₂ x₂}
  → {C : Set l₃}
  → {f₁ : (x₁ : A₁) → B₁ x₁}
  → {f₂ : (x₂ : A₂) → B₂ x₂}
  → {g₁ : (x₁ : A₁) → (y₁ : B₁ x₁) → C}
  → {g₂ : (x₂ : A₂) → (y₂ : B₂ x₂) → C}
  → DPathmap pa B₁ B₂ pb f₁ f₂
  → HPathmap₂ pa B₁ B₂ pb g₁ g₂
  → HPathmap pa (g₁ ∘ f₁) (g₂ ∘ f₂)
compose-hpathmaps pf pg = λ px → pg px (pf px)

compose-pathmaps : ∀ {l₁} {l₂} {l₃} {A₁ A₂ : Set l₁} (pa : A₁ ≡ A₂)
  → (B₁ : A₁ → Set l₂) (B₂ : A₂ → Set l₂) (pb : HPathmap pa B₁ B₂)
  → (C₁ : (x₁ : A₁) → B₁ x₁ → Set l₃) (C₂ : (x₂ : A₂) → B₂ x₂ → Set l₃)
  → (pc : HPathmap₂ pa B₁ B₂ pb C₁ C₂)
  --→ (pc : ∀ {x₁} {x₂} (px : Heq pa x₁ x₂) → {y₁ : B₁ x₁} {y₂ : B₂ x₂} → Heq (pb px) y₁ y₂ → C₁ x₁ y₁ ≡ C₂ x₂ y₂)
  → (f₁ : (x₁ : A₁) → B₁ x₁)
  → (f₂ : (x₂ : A₂) → B₂ x₂)
  → (g₁ : (x₁ : A₁) → (y₁ : B₁ x₁) → C₁ x₁ y₁)
  → (g₂ : (x₂ : A₂) → (y₂ : B₂ x₂) → C₂ x₂ y₂)
  → (pf : DPathmap pa B₁ B₂ pb f₁ f₂)
  → DPathmap₂ pa B₁ B₂ pb C₁ C₂ pc g₁ g₂
  → DPathmap pa (C₁ ∘ f₁) (C₂ ∘ f₂) (compose-hpathmaps pf pc) (g₁ ∘ f₁) (g₂ ∘ f₂)
compose-pathmaps pa B₁ B₂ pb C₁ C₂ pc f₁ f₂ g₁ g₂ pf pg {x₁} {x₂} px = pg px (pf px)

-- Great, it's a lot of context, but `pg px (pf px)` is exactly the kind of
-- "cong is functions applied to paths" that we wanted. Let's try the
-- pi-cong (λ x y → g x y (f x y)) p
-- case that we were struggling with, but now in this representation.

refl-hpathmap : ∀ {l₁} {l₂} → {A : Set l₁} → {B : Set l₂}
  → (f : A → B) → HPathmap refl f f
refl-hpathmap f refl = refl

refl-hpathmap₂ : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂)
  → {C : Set l₃}
  → (f : (x : A) → B x → C)
  → HPathmap₂ refl B B (refl-hpathmap B) f f
refl-hpathmap₂ B f refl refl = refl

HPathmap₃ : ∀ {l₁} {l₂} {l₃} {l₄}
  → {A₁ A₂ : Set l₁} (pa : A₁ ≡ A₂)
  → (B₁ : A₁ → Set l₂) (B₂ : A₂ → Set l₂) → (pb : HPathmap pa B₁ B₂)
  → (C₁ : (x₁ : A₁) → B₁ x₁ → Set l₃) (C₂ : (x₂ : A₂) → B₂ x₂ → Set l₃)
  → (pc : HPathmap₂ pa B₁ B₂ pb C₁ C₂)
  → {D : Set l₄}
  → ((x : A₁) → (y : B₁ x) → C₁ x y → D)
  → ((x : A₂) → (y : B₂ x) → C₂ x y → D)
  → Set _
HPathmap₃ pa B₁ B₂ pb C₁ C₂ pc f₁ f₂
  = ∀ {x₁} {x₂} (px : Heq pa x₁ x₂) → HPathmap₂ (pb px) (C₁ x₁) (C₂ x₂) (pc px) (f₁ x₁) (f₂ x₂)

refl-hpathmap₃ : ∀ {l₁} {l₂} {l₃} {l₄} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → B x → Set l₃)
  → {D : Set l₄}
  → (f : (x : A) → (y : B x) → C x y → D)
  → HPathmap₃ refl B B (refl-hpathmap B) C C (refl-hpathmap₂ B C) f f
refl-hpathmap₃ B C f refl refl refl = refl

refl-pathmap₂ : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → B x → Set l₃)
  → (f : (x : A) → (y : B x) → C x y)
  → DPathmap₂ refl B B (refl-hpathmap B) C C (refl-hpathmap₂ B C) f f
refl-pathmap₂ B C f refl refl = refl

cong-lambda-apply-hom : ∀ {l₁} {l₂} {l₃} {l₄} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → (B x) → Set l₃)
  → {D : Set l₄}
  → (f : (x : A) → (y : B x) → C x y) → (g : (x : A) → (y : B x) → C x y → D)
  → HPathmap₂ refl
              B B (refl-hpathmap B)
              (λ x y → g x y (f x y)) (λ x y → g x y (f x y))
cong-lambda-apply-hom B C {D} f g px py = (refl-hpathmap₃ B C g) px py ((refl-pathmap₂ B C f) px py)

DPathmap₃ : ∀ {l₁} {l₂} {l₃} {l₄}
  → {A₁ A₂ : Set l₁} (pa : A₁ ≡ A₂)
  → (B₁ : A₁ → Set l₂) (B₂ : A₂ → Set l₂) → (pb : HPathmap pa B₁ B₂)
  → (C₁ : (x₁ : A₁) → B₁ x₁ → Set l₃) (C₂ : (x₂ : A₂) → B₂ x₂ → Set l₃)
  → (pc : HPathmap₂ pa B₁ B₂ pb C₁ C₂)
  → (D₁ : (x₁ : A₁) → (y₁ : B₁ x₁) → C₁ x₁ y₁ → Set l₄)
  → (D₂ : (x₂ : A₂) → (y₂ : B₂ x₂) → C₂ x₂ y₂ → Set l₄)
  → (pd : HPathmap₃ pa B₁ B₂ pb C₁ C₂ pc D₁ D₂)
  → ((x : A₁) → (y : B₁ x) → (z : C₁ x y) → D₁ x y z)
  → ((x : A₂) → (y : B₂ x) → (z : C₂ x y) → D₂ x y z)
  → Set _
DPathmap₃ pa B₁ B₂ pb C₁ C₂ pc D₁ D₂ pd f₁ f₂
  = ∀ {x₁} {x₂} (px : Heq pa x₁ x₂) → DPathmap₂ (pb px) (C₁ x₁) (C₂ x₂) (pc px) (D₁ x₁) (D₂ x₂) (pd px) (f₁ x₁) (f₂ x₂)

refl-pathmap₃ : ∀ {l₁} {l₂} {l₃} {l₄} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → B x → Set l₃)
  → (D : (x : A) → (y : B x) → C x y → Set l₄)
  → (f : (x : A) → (y : B x) → (z : C x y) → D x y z)
  → DPathmap₃ refl B B (refl-hpathmap B) C C (refl-hpathmap₂ B C) D D (refl-hpathmap₃ B C D) f f
refl-pathmap₃ B C D f refl refl refl = refl

pi-cong-lambda-apply : ∀ {l₁} {l₂} {l₃} {l₄} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → (B x) → Set l₃)
  → (D : (x : A) → (y : B x) → C x y → Set l₄)
  → (f : (x : A) → (y : B x) → C x y) → (g : (x : A) → (y : B x) → (z : C x y) → D x y z)
  → DPathmap₂ refl
              B B (refl-hpathmap B)
              (λ x y → D x y (f x y)) (λ x y → D x y (f x y)) (cong-lambda-apply-hom B C f D)
              (λ x y → g x y (f x y)) (λ x y → g x y (f x y))
pi-cong-lambda-apply B C D f g px py = refl-pathmap₃ B C D g px py (refl-pathmap₂ B C f px py)

