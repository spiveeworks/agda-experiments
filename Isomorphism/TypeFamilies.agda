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
  → {x₁ x₂ : A} →  (f : (x : A) → B x) → (p : x₁ ≡ x₂)
  → transp B p (f x₁) ≡ f x₂
pi-cong _ _ refl = refl

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
        (pi-pointwise₁ B C p (f x₁) (f x₂) (pi-cong (λ x → B x → C x) f p) y)

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


-- Really we have just decomposed het-cong into pi-cong operations, so we could
-- think about how to implement pi-cong recursively instead.

-- Ultimately in lambda calculus we need to handle three cases of expression,
-- lambda abstraction, function application, and variables. Function
-- application is pretty similar to het-cong, so we can almost use it
-- co-recursively.

pi-cong-apply-easy : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) -> Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → B x) → (g : (x : A) → (y : B x) -> C x)
  → transp (\x -> C x) p (g x₁ (f x₁)) ≡ g x₂ (f x₂)
pi-cong-apply-easy B C {x₁} {x₂} p f g = het-cong B C p g (f x₁) (f x₂) (pi-cong B f p)

-- But what if C depends on B?

pi-cong-apply-direct : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) -> (B x) → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → B x) → (g : (x : A) → (y : B x) -> C x y)
  → transp (λ x → C x (f x)) p (g x₁ (f x₁)) ≡ g x₂ (f x₂)
pi-cong-apply-direct _ _ refl _ _ = refl

-- One way could be to generalize het-cong, but first we need to even work out
-- what heterogeneous transport to dependent types looks like??
transp-dep : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → B x → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → {y₁ : B x₁} → {y₂ : B x₂} → transp B p y₁ ≡ y₂
  → C x₁ y₁ → C x₂ y₂
transp-dep B C p {y₁} {y₂} q z = transp (λ T → T) (het-cong-hom B _ p C y₁ y₂ q) z

-- Then we could define het-cong on pi types like this:
het-pi-cong-direct : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂)
  (C : (x : A) → B x → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → (y : B x) → C x y) → (y₁ : B x₁) → (y₂ : B x₂)
  → (q : transp B p y₁ ≡ y₂) → transp-dep B C p q (f x₁ y₁) ≡ f x₂ y₂
het-pi-cong-direct B C refl f _ _ refl = refl

-- But this transports along the path `het-cong-hom B Type p C q`, whereas we
-- want a heterogeneous equality that transports along cong (λ x → C x (f x)) p
-- we could first compute down this path, and then try to work out a series of
-- rewrites of the LHS that follow along this path.

pi-cong-goal : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) -> (B x) → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → B x) → (g : (x : A) → (y : B x) -> C x y)
  → cong (λ x → C x (f x)) p ≡ het-cong-hom B _ p C (f x₁) (f x₂) (pi-cong B f p)
pi-cong-goal B C refl f g = refl

-- This is just transp-dep anyway... So we should transport along each step of
-- het-cong-hom, rewriting LHS as we go. That is, we should calculate
-- heterogeneous equalities that correspond to the homogeneous equalities we
-- reduced to before, and compose them to a heterogeneous equality along that
-- whole path, i.e. along het-cong-hom.

transp-transp : ∀ {l} {A B C : Set l} (p₁ : A ≡ B) (p₂ : B ≡ C)
  → (x : A)
  → transp (λ T → T) (trans p₁ p₂) x ≡ transp (λ T → T) p₂ (transp (λ T → T) p₁ x)
transp-transp p₁ refl x = refl

het-trans : ∀ {l} {A B C : Set l} (p₁ : A ≡ B) (p₂ : B ≡ C)
  → {x : A} {y : B} {z : C}
  → (q₁ : transp (λ T → T) p₁ x ≡ y)
  → (q₂ : transp (λ T → T) p₂ y ≡ z)
  → transp (λ T → T) (trans p₁ p₂) x ≡ z
het-trans p₁ p₂ q₁ q₂ = trans (transp-transp p₁ p₂ _)
                              (trans (cong (transp (λ T → T) p₂) q₁)
                                     q₂)

het-transp-commute : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂) (C : (x : A) → B x → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂) → (f : (x : A) → (y : B x) → C x y) → (y : B x₁) →
  transp (λ T → T) (transp-commute-hom B _ p C y) (f x₁ y) ≡ f x₂ (transp B p y)
het-transp-commute B C refl f y = refl

-- Now that we are working with primitive transports, we need primitive pi-cong
pi-cong′ : ∀ {l₁} {l₂} {A : Set l₁} (B : A → Set l₂)
  → {x₁ x₂ : A} →  (f : (x : A) → B x) → (p : x₁ ≡ x₂)
  → transp (λ T → T) (cong B p) (f x₁) ≡ f x₂
pi-cong′ _ _ refl = refl

het-pi-cong : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂)
  (C : (x : A) → B x → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → (y : B x) → C x y) → (y₁ : B x₁) → (y₂ : B x₂)
  → (q : transp B p y₁ ≡ y₂) → transp-dep B C p q (f x₁ y₁) ≡ f x₂ y₂
het-pi-cong B C p f y₁ y₂ q = het-trans (transp-commute-hom B _ p C y₁)
                                        (cong (C _) q)
                                        (het-transp-commute B C p f y₁)
                                        (pi-cong′ (λ y → C _ y) (f _) q)

-- We could split this up further, into the individual steps of transp-commute,
-- but for now we get the idea. Let's just see that the pi-cong case we were
-- considering can be computed with this.

pi-cong-apply : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) -> (B x) → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → B x) → (g : (x : A) → (y : B x) -> C x y)
  → transp-dep B C p (pi-cong B f p) (g x₁ (f x₁)) ≡ g x₂ (f x₂)
pi-cong-apply B C {x₁} {x₂} p f g = het-pi-cong B C p g (f x₁) (f x₂) (pi-cong B f p)

-- The other main case to consider is lambda abstraction.

pi-cong-lambda-direct : ∀ {l₁} {l₂} {l₃} {l₄} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → (B x) → Set l₃)
  → (D : (x : A) → (y : B x) → C x y → Set l₄)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → (y : B x) → C x y)
  → transp (λ x → (y : B x) → C x y) p (f x₁) ≡ f x₂
pi-cong-lambda-direct B C D refl f = refl

-- Let's see if we can compute this goal down to something less abstract.

-- We want to compute this goal down to
-- (λ y → f x₁ (transp B (sym p) y)) ≡ (λ y → g x₂ y (f x₂ y))
-- but the LHS has type (y : B x₂) → C x₁ (transp B (sym p) y)
-- while the RHS has type C x₁ y
-- we can treat this as a dependent transport, transporting x₁ to x₂, and
-- (transp B (sym p) y) to y, but then we need a proof that (transp B (sym p) y)
-- is heterogeneously equal to y, i.e. that transp B p (transp B (sym p) y) ≡ y
-- i.e. that transporting over p is the inverse of transporting over (sym p)

transp-sym : ∀ {l₁} {l₂} {A : Set l₁} (B : A → Set l₂)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (y : B x₂)
  → transp B p (transp B (sym p) y) ≡ y
transp-sym _ refl _ = refl

pi-cong-lambda-step : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → (B x) → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → (y : B x) → C x y)
  → transp (λ x → (y : B x) → C x y) p (f x₁) ≡ (λ y → transp-dep B C p (transp-sym B p y) (f x₁ (transp B (sym p) y)))
pi-cong-lambda-step B C refl f = refl

-- Then weakening our goal down to a pointwise proof, we can use het-pi-cong,
-- similar to what we did for the application case.

pi-cong-lambda : ∀ {l₁} {l₂} {l₃} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → (B x) → Set l₃)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → (y : B x) → C x y)
  → (y₂ : B x₂)
  → transp-dep B C p (transp-sym B p y₂) (f x₁ (transp B (sym p) y₂)) ≡ f x₂ y₂
pi-cong-lambda B C p f y₂ = het-pi-cong B C p f (transp B (sym p) y₂) y₂ (transp-sym B p y₂)

-- This seems neat, but it didn't actually do anything... het-pi-cong itself
-- applies pi-cong to f, to show that f commutes with transp B...

-- Perhaps we need to assume y is in the context, and directly generalize our
-- apply case to take y into account:

pi-cong-lambda-apply-direct : ∀ {l₁} {l₂} {l₃} {l₄} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → (B x) → Set l₃)
  → (D : (x : A) → (y : B x) → C x y → Set l₄)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → (y : B x) → C x y) → (g : (x : A) → (y : B x) -> (z : C x y) → D x y z)
  → transp (λ x → (y : B x) → D x y (f x y)) p (λ y → g x₁ y (f x₁ y)) ≡ (λ y → g x₂ y (f x₂ y))
pi-cong-lambda-apply-direct B C D refl f g = refl

-- Expanding this goal, we get
pi-cong-lambda-apply-direct₂ : ∀ {l₁} {l₂} {l₃} {l₄} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → (B x) → Set l₃)
  → (D : (x : A) → (y : B x) → C x y → Set l₄)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → (y : B x) → C x y) → (g : (x : A) → (y : B x) -> (z : C x y) → D x y z)
  → (y₂ : B x₂)
  → transp-dep B (λ x y → D x y (f x y)) p
               (transp-sym B p y₂)
               (g x₁ (transp B (sym p) y₂) (f x₁ (transp B (sym p) y₂)))
    ≡ g x₂ y₂ (f x₂ y₂)
pi-cong-lambda-apply-direct₂ B C D refl f g y = refl

-- but we haven't even separated out the f x₁ y ≡ f x₂ y from the
-- g x₁ y z₁ ≡ g x₂ y z₂.
-- We could use transp-dep on transp-sym to show f x₁ (transp B (sym p) y) ≡ f x₂ y,
-- and then make a transp-dep₂ that transports along a transp-dep??

het-cong₂-hom : ∀ {l₁} {l₂} {l₃} {l₄} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → B x → Set l₃) (D : Set l₄)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → (f : (x : A) → (y : B x) → C x y → D)
  → (y₁ : B x₁) → (y₂ : B x₂) → (q : transp B p y₁ ≡ y₂)
  → (z₁ : C x₁ y₁) → (z₂ : C x₂ y₂) → (transp-dep B C p q z₁ ≡ z₂)
  → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
het-cong₂-hom B C D refl f _ _ refl _ _ refl = refl

transp-dep₂-path : ∀ {l₁} {l₂} {l₃} {l₄} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → B x → Set l₃)
  → (D : (x : A) → (y : B x) → C x y → Set l₄)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → {y₁ : B x₁} → {y₂ : B x₂} → (q : transp B p y₁ ≡ y₂)
  → {z₁ : C x₁ y₁} → {z₂ : C x₂ y₂} → transp-dep B C p q z₁ ≡ z₂
  → D x₁ y₁ z₁ ≡ D x₂ y₂ z₂
transp-dep₂-path B C D p q r = het-cong₂-hom B C _ p D _ _ q _ _ r

transp-dep₂ : ∀ {l₁} {l₂} {l₃} {l₄} {A : Set l₁} (B : A → Set l₂)
  → (C : (x : A) → B x → Set l₃)
  → (D : (x : A) → (y : B x) → C x y → Set l₄)
  → {x₁ x₂ : A} → (p : x₁ ≡ x₂)
  → {y₁ : B x₁} → {y₂ : B x₂} → (q : transp B p y₁ ≡ y₂)
  → {z₁ : C x₁ y₁} → {z₂ : C x₂ y₂} → transp-dep B C p q z₁ ≡ z₂
  → D x₁ y₁ z₁ → D x₂ y₂ z₂
transp-dep₂ B C D p q r w₁ = transp (λ T → T) (transp-dep₂-path B C D p q r) w₁

-- Perhaps we could continue, deriving what we have done so far but with an
-- extra level of indirection... But it's so confusing having this y₂ and
-- (transp B (sym p) y₂) stuff around, is this a path? Do we want to compute on
-- it? The whole goal of congruence is to compute on paths, but since we are
-- assuming that extensionality and congruence are be radically separate
-- properties, it becomes confusing what path we are supposed to be computing.
-- Maybe we should define a path between f₁ and f₁ to be a function that maps
-- paths x₁ ≡ x₂ to paths f₁ x₁ ≡ f₂ x₂, and then if our functions are λx₁→x₁,
-- and λx₂→x₂, then our path map should be λ x₁ x₂ p → p... Ignore the
-- homogeneous case, and only consider how heterogeneous interacts with
-- heterogeneous, it might actually save us from having to consider one level
-- of indirection altogether? Let's try this in PathMaps.agda

