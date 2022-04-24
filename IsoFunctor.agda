Type : Set₁
Type = Set

Kind : Set₂
Kind = Set₁

id : ∀ {A : Type} → A → A
id x = x

data _≡_ {A : Type} (x : A) : A → Set where
  refl : x ≡ x

trans : ∀ {A} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans xeqy refl = xeqy

cong : ∀ {A} {B} → {x y  : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

record _≅_ (A B : Type) : Type where
  field
    fwd : A → B
    bwd : B → A
    fwdbwd : ∀ x → bwd (fwd x) ≡ x
    bwdfwd : ∀ y → fwd (bwd y) ≡ y

refl-iso : ∀ A → A ≅ A
refl-iso A = record {fwd = id; bwd = id; fwdbwd = λ x → refl; bwdfwd = λ y → refl}

inv-iso : ∀ {A} {B} → A ≅ B → B ≅ A
inv-iso record{fwd = fwd; bwd = bwd; fwdbwd = fwdbwd; bwdfwd = bwdfwd} = record{fwd = bwd; bwd = fwd; fwdbwd = bwdfwd; bwdfwd = fwdbwd}

IsStructural : (F : Type → Type) → Kind
IsStructural F = ∀ A B → A ≅ B → F A ≅ F B

I : Type → Type
I A = A

K : Type → Type → Type
K A B = A

id-structural : IsStructural I
id-structural A B iso = iso

const-structural : ∀ A → IsStructural (K A)
const-structural A _ _ _ = refl-iso A

Exp : (F G : Type → Type) → Type → Type
Exp F G A = F A → G A

exp-fwd : ∀ {F} {G} → IsStructural F → IsStructural G → ∀ {A} {B} → A ≅ B → (F A → G A) → (F B → G B)
exp-fwd Fstr Gstr iso f ys = fwd Giso (f (bwd Fiso ys))
  where open _≅_
        Fiso = Fstr _ _ iso
        Giso = Gstr _ _ iso

exp-bwd : ∀ {F} {G} → IsStructural F → IsStructural G → ∀ {A} {B} → A ≅ B → (F B → G B) → (F A → G A)
exp-bwd Fstr Gstr iso g xs = bwd Giso (g (fwd Fiso xs))
  where open _≅_
        Fiso = Fstr _ _ iso
        Giso = Gstr _ _ iso

exp-fwdbwd : ∀ {F} {G} Fstr Gstr {A} {B} iso f ys → (exp-bwd {F} {G} Fstr Gstr {A} {B} iso (exp-fwd {F} {G} Fstr Gstr {A} {B} iso f)) ys ≡ f ys
exp-fwdbwd Fstr Gstr iso f ys = trans (fwdbwd Giso _) (cong f (fwdbwd Fiso _))
  where open _≅_
        Fiso = Fstr _ _ iso
        Giso = Gstr _ _ iso

exp-bwdfwd : ∀ {F} {G} Fstr Gstr {A} {B} iso g xs → (exp-fwd {F} {G} Fstr Gstr {A} {B} iso (exp-bwd {F} {G} Fstr Gstr {A} {B} iso g)) xs ≡ g xs
exp-bwdfwd Fstr Gstr iso g xs = trans (bwdfwd Giso _) (cong g (bwdfwd Fiso _))
  where open _≅_
        Fiso = Fstr _ _ iso
        Giso = Gstr _ _ iso

postulate
  ext : ∀ {A B : Set} → {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

exp-str : ∀ {F} {G} → IsStructural F → IsStructural G → IsStructural (Exp F G)
exp-str Fstr Gstr A B iso = record{
    fwd = exp-fwd Fstr Gstr iso;
    bwd = exp-bwd Fstr Gstr iso;
    fwdbwd = λ f → ext (exp-fwdbwd Fstr Gstr iso f);
    bwdfwd = λ g → ext (exp-bwdfwd Fstr Gstr iso g) }
