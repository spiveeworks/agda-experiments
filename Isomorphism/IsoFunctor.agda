open import Basics

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


IsTrivial : Type → Type
IsTrivial A = ∀ (x y : A) → x ≡ y

trivial-map : ∀ {A} {B} → A ≅ B → IsTrivial A → IsTrivial B
trivial-map iso trx y₁ y₂ = trans (trans y₁-x₁ x₁-x₂) x₂-y₂
  where
    open _≅_
    y₁-x₁ : y₁ ≡ fwd iso (bwd iso y₁)
    x₁-x₂ : fwd iso (bwd iso y₁) ≡ fwd iso (bwd iso y₂)
    x₂-y₂ : fwd iso (bwd iso y₂) ≡ y₂

    y₁-x₁ = sym (bwdfwd iso y₁)
    x₁-x₂ = cong (fwd iso) (trx (bwd iso y₁) (bwd iso y₂))
    x₂-y₂ = bwdfwd iso y₂

trivial-iso : ∀ {A} {B} → IsTrivial A → IsTrivial B → (A → B) → (B → A) → A ≅ B
trivial-iso trx try fwd bwd = record{fwd = fwd; bwd = bwd; fwdbwd = λ x → trx _ _; bwdfwd = λ y → try _ _}

