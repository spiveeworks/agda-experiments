open import Basics

-- When implementing function extensionality, higher inductive types, and
-- univalence, one must work out when to evaluate J elimination rules directly.
-- Say we have some interval type I with (i0 i1 : I) and (p : i0 ≡ i1), and
-- want to transport along a path (path : I → A), then path must have defined
-- an equality between (path i0) and (path i1) in order to type check, so if we
-- have some type family (T : A → Type), then we can map (T (path i₀)) to
-- (T (path i₁)), using (cong T (cong path p)) as the path to transport along.
-- In this way we divide path computations into two steps, first we try to
-- simplify `cong <type family> <path>` as much as we can, and then if it is
-- refl or an isomorphism then we evaluate the actual transport.
--
-- This seems easy enough, but in actual J elimination we need to handle type
-- families that take the path as an input as well,
-- (T : (x : A) → x₁ ≡ x → Type), something like...

J-path : ∀ {A : Type} {x₁ : A} → (M : (x : A) → x₁ ≡ x → Type)
  → (x₂ : A) → (p : x₁ ≡ x₂) → M x₁ refl ≡ M x₂ p
J-path _ _ refl = refl

-- This is a start, but what we really want is a recursive relationship that
-- lets us compute the type path one subexpression at a time. Say we have some
-- simple function `f` that has been type checked to be a valid functor on
-- homotopy types, then we can apply `cong f` to the path beneath it, to work
-- out the path for this subexpression of the type family.

het-cong-direct : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂) (C : A → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → B x → C x) → (y₁ : B x₁) → (y₂ : B x₂)
  → transp B p y₁ ≡ y₂ → transp C p (f x₁ y₁) ≡ f x₂ y₂
het-cong-direct B C refl f _ _ refl = refl

-- It would be nice to know in more detail what this step looks like. If we are
-- mapping y₁ and y₂ to f(x₁, y₁) and f(x₂, y₂), then we want a path from
-- transp(f(x₁, y₁)) to f(x₂, y₂). If the path from `transp(y₁)` to `y₂` was `q`, then
-- we can get part of the way with `cong (f x₂) q : f(transp(y₁)) ≡ f(y₂)`, but we
-- need to also extract a path from `transp(f(y₁))` to `f(transp(y₁))`.

transp-commute : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂) (C : A → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂) → (f : (x : A) → B x → C x) → (y : B x₁) →
  transp C p (f x₁ y) ≡ f x₂ (transp B p y)
transp-commute _ _ refl _ _ = refl

het-cong : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂) (C : A → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → B x → C x) → (y₁ : B x₁) → (y₂ : B x₂)
  → transp B p y₁ ≡ y₂ → transp C p (f x₁ y₁) ≡ f x₂ y₂
het-cong B C p f y₁ y₂ q = trans (transp-commute B C p f y₁) (cong (f _) q)

-- We can actually use `cong f p` to find the path in transp-commute

pi-cong : ∀ {l₁} {l₂} {A : Set l₁} (B : A → Set l₂)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂) → (f : (x : A) → B x) →
  transp B p (f x₁) ≡ f x₂
pi-cong _ refl _ = refl

-- This tells us that the functions (functors) `f x₁` and `f x₂` are
-- heterogenously equal, but how do we apply equal functions to different
-- types? We can transport the function forward

pi-pointwise₁ : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂) (C : A → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂) → (f₁ : B x₁ → C x₁) → (f₂ : B x₂ → C x₂)
  → transp (λ x → B x → C x) p f₁ ≡ f₂
  → ∀ y → transp (λ x → B x → C x) p f₁ (transp B p y) ≡ f₂ (transp B p y)
pi-pointwise₁ B C p _ _ q y = cong (λ f → f (transp B p y)) q

-- If we transport a function and its argument, surely we can just calculate it
-- on the spot, and transport the result.

pointwise-squash : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂) (C : A → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂) → (f : B x₁ → C x₁)
  → ∀ y → transp (λ x → B x → C x) p f (transp B p y) ≡ transp C p (f y)
pointwise-squash B C refl f y = refl

-- Maybe you even want to do this in one step instead? Depends how each looks
-- when implemented.

pi-pointwise₂ : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂) (C : A → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂) → (f₁ : B x₁ → C x₁) → (f₂ : B x₂ → C x₂)
  → transp (λ x → B x → C x) p f₁ ≡ f₂
  → ∀ y → transp C p (f₁ y) ≡ f₂ (transp B p y)
pi-pointwise₂ B C refl _ _ q y = cong (λ f → f y) q

-- However you do it, you can then use this to find our commuting result
-- explicitly.

transp-commute₂ : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂) (C : A → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂) → (f : (x : A) → B x → C x) → (y : B x₁) →
  transp C p (f x₁ y) ≡ f x₂ (transp B p y)
transp-commute₂ B C {x₁} {x₂} p f y =
  trans (sym (pointwise-squash B C p (f x₁) y))
        (pi-pointwise₁ B C p (f x₁) (f x₂) (pi-cong (λ x → B x → C x) p f) y)

-- Now at some point the subexpressions must stop being heterogeneously equal,
-- since at the very end their type is going to be Type, so at any point we
-- could close up into a homogeneous equality, and just use homogeneous cong
-- from there. (Conversely we could get lambdas that introduce more dependently
-- typed variables, but that is beyond the scope of this experiment.)

transp-commute-hom : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂) (C : Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂) → (f : (x : A) → B x → C) → (y : B x₁) →
  f x₁ y ≡ f x₂ (transp B p y)
transp-commute-hom _ _ refl _ _ = refl

het-cong-hom : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂) (C : Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → B x → C) → (y₁ : B x₁) → (y₂ : B x₂)
  → transp B p y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
het-cong-hom B C p f y₁ y₂ q = trans (transp-commute-hom B C p f y₁) (cong (f _) q)

-- Now let's try using this expression logic to decompose a simple theorem into
-- a cong step and a transport step. First, the direct implementation of the
-- theorem:

thm : ∀ {A : Type} {x₁ x₂ : A} (p : x₁ ≡ x₂) → trans p (sym p) ≡ refl
thm refl = refl

-- Next we try building a path from the left hand side with refl, to the left
-- hand side with p.

thm-lhs : ∀ {A : Type} {x₁ : A} → (x : A) → x₁ ≡ x → x₁ ≡ x₁
thm-lhs _ p = trans p (sym p)

-- Initialise a heterogeneous path that we can use to build up subexpressions.

thm-base : ∀ {A : Type} {x₁ x₂ : A} →
  (p : x₁ ≡ x₂) → transp (λ x → x₁ ≡ x) p refl ≡ p
thm-base refl = refl

-- This sort of thing could be done level by level, but this demonstrates the
-- point just fine.

thm-step-1 : ∀ {A : Type} {x₁ x₂ : A} →
  (p : x₁ ≡ x₂) → transp (λ _ → x₁ ≡ x₁) p (thm-lhs x₁ refl) ≡ thm-lhs x₂ p
thm-step-1 {x₁ = x₁} p = het-cong (λ x → x₁ ≡ x) (λ _ → x₁ ≡ x₁) p thm-lhs refl p (thm-base p)

-- Next we try building up to the final goal, the Type itself, ready to be
-- transported.

thm-goal : ∀ {A : Type} {x₁ : A} → (x : A) → x₁ ≡ x → Type
thm-goal _ p = trans p (sym p) ≡ refl

thm-step-2 : ∀ {A : Type} {x₁ x₂ : A} →
  (p : x₁ ≡ x₂) → thm-goal x₁ refl ≡ thm-goal x₂ p
thm-step-2 {x₁ = x₁} p = het-cong-hom (λ x → x₁ ≡ x) Type p thm-goal refl p (thm-base p)

-- check that this type actually provides the path we wanted

thm-step-3 : ∀ {A : Type} {x₁ x₂ : A} →
  (p : x₁ ≡ x₂) → (refl {x = x₁} ≡ refl) ≡ thm-goal x₂ p
thm-step-3 p = thm-step-2 p

-- now use this path to turn `refl` into something useful.

thm-decompose : ∀ {A : Type} {x₁ x₂ : A} →
  (p : x₁ ≡ x₂) → trans p (sym p) ≡ refl
thm-decompose p = transp (λ T → T) (thm-step-3 p) refl

-- This is easy to generalize like this:

J-path-decompose : ∀ {A : Type} {x₁ : A} → (M : (x : A) → x₁ ≡ x → Type)
  → (x₂ : A) → (p : x₁ ≡ x₂) → M x₁ refl ≡ M x₂ p
J-path-decompose {x₁ = x₁} M x₂ p = het-cong-hom (λ x → x₁ ≡ x) Type p M refl p (thm-base p)

J-decompose : ∀ {A : Type} {x₁ : A} → (M : (x : A) → x₁ ≡ x → Type)
  → (M x₁ refl) → (x₂ : A) → (p : x₁ ≡ x₂) → M x₂ p
J-decompose {x₁ = x₁} M m x₂ p = transp (λ T → T) (J-path M x₂ p) m

