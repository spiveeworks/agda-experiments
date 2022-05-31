open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

module Models.SimplyTyped (typevars : Nat) where

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
if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
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

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _::_ : ∀ {n} → A → Vec A n → Vec A (suc n)

infix 4 _!!_

_!!_ : ∀ {n} {A} → Vec A n → Fin n → A
[] !! ()
(x :: xs) !! fzero = x
(x :: xs) !! (fsuc i) = xs !! i

Typevar : Set
Typevar = Fin typevars

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

data TypeCheck {vars} (ctx : Vec Type vars) (x : Expr vars) : Set where
  success : (T : Type) → given ctx expr x has-type T → TypeCheck ctx x
  failure : ((T : Type) → given ctx expr x has-type T → Void) → TypeCheck ctx x

types-are-unique : ∀ {vars} (ctx : Vec Type vars) x {T₁} {T₂}
  → given ctx expr x has-type T₁ → given ctx expr x has-type T₂ → T₁ ≡ T₂
types-are-unique ctx (Var i) varty varty = refl
types-are-unique ctx (Lambda A x) (lambdaty p₁) (lambdaty p₂) =
  cong (A [→]_) (types-are-unique (A :: ctx) x p₁ p₂)
types-are-unique ctx (Apply f x) (apply-ty pf₁ px₁) (apply-ty pf₂ px₂) =
    equal-codomains (types-are-unique ctx f pf₁ pf₂)

compare-types : ∀ {vars} (ctx : Vec Type vars) x T
  → TypeCheck ctx x → Dec (given ctx expr x has-type T)
compare-types ctx x T (failure disproof) = false ⊣ λ p → disproof T p
compare-types ctx x T₁ (success T₂ p₂) with tydec T₁ T₂
... | true ⊣ refl = true ⊣ p₂
... | false ⊣ nt = false ⊣ λ p₁ → nt (types-are-unique ctx x p₁ p₂)

types-cant-differ : ∀ {vars} (ctx : Vec Type vars) x {a} {A} {B}
  → given ctx expr x has-type (var a) → given ctx expr x has-type (A [→] B) → Void
types-cant-differ ctx x p₁ p₂ with types-are-unique ctx x p₁ p₂
... | ()

type-check : ∀ {vars} ctx x → TypeCheck {vars} ctx x
type-check ctx (Var i) = success (ctx !! i) varty
type-check ctx (Lambda A x) with type-check (A :: ctx) x
... | failure np = failure λ {(A [→] B) (lambdaty p) → np _ p}
... | success B p = success (A [→] B) (lambdaty p)
type-check ctx (Apply f x) with type-check ctx f | type-check ctx x
... | failure npf | _ = failure λ {B (apply-ty pf px) → npf _ pf}
... | _ | failure npx = failure λ {B (apply-ty pf px) → npx _ px}
... | success (var a) pf₁ | _ = failure
  λ {B (apply-ty pf₂ px) → types-cant-differ _ _ pf₁ pf₂}
... | success (A₁ [→] B) pf | success A₂ px with tydec A₁ A₂
...     | false ⊣ neq = failure λ {A₃ (apply-ty pf₃ px₃)
    → neq (trans (equal-domains (types-are-unique _ _ pf pf₃))
                 (types-are-unique _ _ px₃ px))}
...     | true ⊣ refl = success B (apply-ty pf px)


