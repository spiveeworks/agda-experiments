open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

module Models.SimplyTyped {typevars : Nat} where

infixr 5 _and_

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ {x} → x ≡ x

sym : ∀ {A} → {x₁ x₂ : A} → x₁ ≡ x₂ → x₂ ≡ x₁
sym refl = refl

trans : ∀ {A} → {x₁ x₂ x₃ : A} → x₁ ≡ x₂ → x₂ ≡ x₃ → x₁ ≡ x₃
trans p refl = p

cong : ∀ {A} {B} → (f : A → B) → {x₁ x₂ : A} → x₁ ≡ x₂ → f x₁ ≡ f x₂
cong f refl = refl

_and_ : Bool → Bool → Bool
false and _ = false
true and b = b

infix 0 if_then_else_
if_then_else_ : ∀ {l} {A : Set l} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

data Void : Set where

data IsFalse : Bool → Set where
  ff : IsFalse false

infix 0 _⊣_
record Dec (A : Set) : Set where
  constructor _⊣_
  field
    value : Bool
    proof : if value then A else (A → Void)

data Fin : Nat → Set where
  fzero : ∀ {n} → Fin (suc n)
  fsuc : ∀ {n} → Fin n → Fin (suc n)

pred-eq : ∀ {n} → {i j : Fin n} → fsuc i ≡ fsuc j → i ≡ j
pred-eq refl = refl

findec : ∀ {n} → (i j : Fin n) → Dec (i ≡ j)
findec fzero fzero = true ⊣ refl
findec (fsuc i) (fsuc j) with findec i j
...                         | true ⊣ refl = true ⊣ refl
...                         | false ⊣ neq = false ⊣ λ p → neq (pred-eq p)
findec fzero (fsuc _) = false ⊣ λ ()
findec (fsuc _) fzero = false ⊣ λ ()

infixr 5 _::_

data Vec {l} (A : Set l) : Nat → Set l where
  [] : Vec A zero
  _::_ : ∀ {n} → A → Vec A n → Vec A (suc n)

infix 4 _!!_

_!!_ : ∀ {l} {n} {A : Set l} → Vec A n → Fin n → A
[] !! ()
(x :: xs) !! fzero = x
(x :: xs) !! (fsuc i) = xs !! i

Typevar : Set
Typevar = Fin typevars

infixr 20 _[→]_

data Type : Set where
  _[→]_ : Type → Type → Type
  var : Typevar → Type

equal-domains : ∀ {A₁ A₂ B₁ B₂ : Type} → (A₁ [→] B₁) ≡ (A₂ [→] B₂) → A₁ ≡ A₂
equal-domains refl = refl

equal-codomains : ∀ {A₁ A₂ B₁ B₂ : Type} → (A₁ [→] B₁) ≡ (A₂ [→] B₂) → B₁ ≡ B₂
equal-codomains refl = refl

equal-indices : ∀ {i j : Typevar} → var i ≡ var j → i ≡ j
equal-indices refl = refl

tydec : ∀ (T₁ T₂ : Type) → Dec (T₁ ≡ T₂)
tydec (A₁ [→] B₁) (A₂ [→] B₂) with tydec A₁ A₂ | tydec B₁ B₂
...                              | true ⊣ refl | true ⊣ refl = true ⊣ refl
...                              | false ⊣ nA | _ = false ⊣ λ p → nA (equal-domains p)
...                              | _ | false ⊣ nB = false ⊣ λ p → nB (equal-codomains p)
tydec (var i) (var j) with findec i j
...                      | true ⊣ refl = true ⊣ refl
...                      | false ⊣ ni = false ⊣ λ p → ni (equal-indices p)
tydec (_ [→] _) (var _) = false ⊣ λ ()
tydec (var _) (_ [→] _) = false ⊣ λ ()

data Expr (vars : Nat) : Set where
  Var : Fin vars → Expr vars
  Lambda : Type → Expr (suc vars) → Expr vars
  Apply : Expr vars → Expr vars → Expr vars

infix -2 given_expr_has-type_
data given_expr_has-type_ {vars} (ctx : Vec Type vars) : Expr vars → Type → Set where
  varty : ∀ {i} → given ctx expr Var i has-type (ctx !! i)
  lambdaty : ∀ {x} {A} {B} → given (A :: ctx) expr x has-type B
    → given ctx expr Lambda A x has-type (A [→] B)
  apply-ty : ∀ {f} {x} {A} {B} → given ctx expr f has-type (A [→] B)
    → given ctx expr x has-type A
    → given ctx expr Apply f x has-type B

record Typechecks {vars} (ctx : Vec Type vars) (x : Expr vars) : Set where
  constructor _[⊣]_
  field
    ty : Type
    derivation : given ctx expr x has-type ty

types-are-unique : ∀ {vars} (ctx : Vec Type vars) x {T₁} {T₂}
  → given ctx expr x has-type T₁ → given ctx expr x has-type T₂ → T₁ ≡ T₂
types-are-unique ctx (Var i) varty varty = refl
types-are-unique ctx (Lambda A x) (lambdaty p₁) (lambdaty p₂) =
  cong (A [→]_) (types-are-unique (A :: ctx) x p₁ p₂)
types-are-unique ctx (Apply f x) (apply-ty pf₁ px₁) (apply-ty pf₂ px₂) =
    equal-codomains (types-are-unique ctx f pf₁ pf₂)

types-cant-differ : ∀ {vars} (ctx : Vec Type vars) x {a} {A} {B}
  → given ctx expr x has-type (var a) → given ctx expr x has-type (A [→] B) → Void
types-cant-differ ctx x p₁ p₂ with types-are-unique ctx x p₁ p₂
... | ()

type-check : ∀ {vars} ctx x → Dec (Typechecks {vars} ctx x)
type-check ctx (Var i) = true ⊣ (ctx !! i) [⊣] varty
type-check ctx (Lambda A x) with type-check (A :: ctx) x
... | false ⊣ np = false ⊣ λ {((A [→] B) [⊣] lambdaty p) → np (_ [⊣] p)}
... | true ⊣ B [⊣] p = true ⊣ (A [→] B) [⊣] lambdaty p
type-check ctx (Apply f x) with type-check ctx f | type-check ctx x
    -- Propogate errors up the tree.
... | false ⊣ npf | _ = false ⊣ λ {(B [⊣] apply-ty pf px) → npf (_ [⊣] pf)}
    -- Can't apply unknown types to things.
... | _ | false ⊣ npx = false ⊣ λ {(B [⊣] apply-ty pf px) → npx (_ [⊣] px)}
    -- Propogate errors up the tree.
... | true ⊣ (var a) [⊣] pf₁ | _ = false ⊣
  λ {(B [⊣] apply-ty pf₂ px) → types-cant-differ _ _ pf₁ pf₂}
... | true ⊣ (A₁ [→] B) [⊣] pf | true ⊣ A₂ [⊣] px with tydec A₁ A₂
        -- Argument is the wrong type.
...     | false ⊣ neq = false ⊣ λ {(A₃ [⊣] apply-ty pf₃ px₃)
    → neq (trans (equal-domains (types-are-unique _ _ pf pf₃))
                 (types-are-unique _ _ px₃ px))}
        -- Everything matches up, continue the derivation!
...     | true ⊣ refl = true ⊣ B [⊣] (apply-ty pf px)


ToSet : ∀ {a} → Vec (Set a) typevars → Type → Set a
ToSet ts (A [→] B) = ToSet ts A → ToSet ts B
ToSet ts (var i) = ts !! i

data Context {a} (tys : Vec (Set a) typevars) : ∀ {n} → Vec Type n → Set a where
  cempty : Context tys {0} []
  cval : ∀ {n} {vt} {vts} → ToSet tys vt → Context tys {n} vts → Context tys (vt :: vts)

ctx-lookup : ∀ {a} {tys} {n} {vts} → Context {a} tys {n} vts
  → (i : Fin n) → ToSet tys (vts !! i)
ctx-lookup (cval val vals) fzero = val
ctx-lookup (cval val vals) (fsuc i) = ctx-lookup vals i

to-function : ∀ {vars} (ctx : Vec Type vars) x T → given ctx expr x has-type T
  → ∀ {a} → (tys : Vec (Set a) typevars) → Context tys ctx → ToSet tys T
to-function ctx (Var i) .(ctx !! i) varty tys vals = ctx-lookup vals i
to-function ctx (Lambda A x) (A [→] B) (lambdaty prf) tys vals val =
  to-function (A :: ctx) x B prf tys (cval val vals)
to-function ctx (Apply f x) B (apply-ty pf px) tys vals =
  to-function ctx f (_ [→] B) pf tys vals
  (to-function ctx x _ px tys vals)

