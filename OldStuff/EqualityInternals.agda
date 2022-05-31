--------------
-- Equality --
--------------

Type : Set₁
-- alias the lowest universe level to 'Type'
Type = Set₀

-- Equality is _defined_ as the relation whose only constructor is refl
-- this makes it the minimal reflexive relation, which lets us derive the rest
data _≡_ {A : Type} : A → A → Type where
    refl : (x : A) → x ≡ x

sym : {A : Type} → {x y : A} → x ≡ y → y ≡ x
-- w type checks as both x and y, meaning w ≡ w is sufficient to prove x ≡ y
sym (refl w) = refl w

trans : {A : Type} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- in fact, x and y are directly replaced with w, so our goal is now w ≡ z
trans (refl w) weqz = weqz

cong : {A B : Type} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
-- replacing x and y with w inside more complex expressions
cong f (refl w) = refl (f w)

subst : {A : Type} → (P : A → Type) → {x y : A} → x ≡ y → P x → P y
subst P (refl w) pw = pw

---------------------
-- Lazy Evaluation --
---------------------

data Bool : Type where
    false : Bool
    true : Bool

not : Bool → Bool
not false = true
not true = false

negfalse-is-true : not false ≡ true
-- type inference can simplify closed expressions, so this type checks
negfalse-is-true = refl true

doubleneg : ∀ x → not (not x) ≡ x
-- each of these branches can directly evaluate the LHS once x is known
doubleneg false = refl false
doubleneg true = refl true

-- type inference can also simplify the type of the RHS, so this type checks
doublenegfalse : false ≡ false
doublenegfalse = doubleneg false

-- since doubleneg false and refl false have the same type, they can be
-- compared using equality
doublenegfalse-is-refl : doubleneg false ≡ refl false
-- not only does the type of doubleneg false compute to false ≡ false,
-- but the value of doubleneg false computes to the relevant branch, which was
-- which was just refl false
doublenegfalse-is-refl = refl (refl false)

-- since doubleneg x : not (not x) ≡ x, and refl x : x ≡ x, we can't actually
-- compare them using equality, this type annotation does NOT type check:
-- doublenegx-is-refl-prop : ∀ x → doubleneg x ≡ refl x
-- the definition might not type check either, but we can't even get to that
-- stage

x-is-notnotx : ∀ x → x ≡ not (not x)
x-is-notnotx x = sym (doubleneg x)

-- let's use subst to turn refl x into a term of type not (not x) ≡ x
refl-as-doubleneg : ∀ x → not (not x) ≡ x
refl-as-doubleneg x = subst (λ y → y ≡ x) (x-is-notnotx x) (refl x) where

-- but now we have another problem, doubleneg x and refl-as-doubleneg x are
-- both complex expressions that must pattern match on many things, so we
-- cannot prove that they are equal by merely invoking refl (refl x),
-- first we must look at how refl-as-doubleneg simplifies when applied to
-- arguments

-- similar to doublenegfalse, the type of the RHS simplifies into false ≡ false
false-is-notnotfalse : false ≡ false
false-is-notnotfalse = x-is-notnotx false

-- once again we can compare this equality to refl, and it works!
false-is-notnotfalse-is-refl : x-is-notnotx false ≡ refl false
-- doubleneg false simplifies into refl false, so goal is
-- sym (refl false) ≡ refl false
-- but, sym can pattern match on refl to become refl false! so our goal is
-- refl false ≡ refl false
false-is-notnotfalse-is-refl = refl (refl false)

-- now our transported refl can also simplify what it type checks as
refl-as-doublenegfalse : false ≡ false
refl-as-doublenegfalse = refl-as-doubleneg false

-- we can compare this to refl as well
refl-as-doublenegfalse-is-refl : refl-as-doubleneg false ≡ refl false
-- x-is-notnotx false simplifies to refl false as seen before,
-- then refl-as-doubleneg false becomes subst P (refl false) (refl false),
-- and subst also pattern matchs on refl, becoming the identity on its next
-- argument, meaning the LHS is once again, refl false :)
refl-as-doublenegfalse-is-refl = refl (refl false)

-- finally we can compare doubleneg x to refl-as-doubleneg x, which is
-- essentially proving the heterogeneous equality doubleneg x ≡ refl x
doubleneg-is-refl : ∀ x → doubleneg x ≡ refl-as-doubleneg x
-- by pattern matching on x, all the equalities turn into refl, magical
doubleneg-is-refl false = refl (refl false)
doubleneg-is-refl true = refl (refl true)

