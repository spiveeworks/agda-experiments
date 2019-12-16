-- universe levels

Kind : Set₂
Kind = Set₁

Type : Kind
Type = Set

-- type constructors

Into : Type -> Type -> Type
Into A T = T -> A

From : Type -> Type -> Type
From A T = A -> T

Double : (Type → Type) → (Type → Type)
Double F T = F (F T)

IntoInto : Type -> Type -> Type
IntoInto A = Double (Into A) -- (T -> A) -> A

-- map (functor)

Map : (Type -> Type) -> Kind
Map F = (A B : Type) -> (A -> B) -> F A -> F B

CoMap : (Type -> Type) -> Kind
CoMap F = (A B : Type) -> (A -> B) -> F B -> F A

map-from : (A : Type) → Map (From A)
map-from A B C f g x = f (g x)

comap-into : (A : Type) -> CoMap (Into A)
comap-into A B C f g x = g (f x)

cocomap : (F : Type → Type) → CoMap F → Map (Double F)
cocomap F comap A B f = comap (F B) (F A) (comap A B f)

map-intointo : (A : Type) → Map (IntoInto A)
map-intointo A = cocomap (Into A) (comap-into A)

-- unit (start of applicative/monad)

MUnit : (Type → Type) → Kind
MUnit F = (A : Type) → A → F A

map→munit : (F : Type → Type) → (Map F) → (A : Type) → F A → MUnit F
map→munit F map A mx B y = map A B (λ x → y) mx

munit-from : (A : Type) → MUnit (From A)
munit-from A B y x = y

munit-intointo : (B : Type) → MUnit (IntoInto B)
munit-intointo B A x f = f x

-- join (monad)

Join : (Type → Type) → Kind
Join F = (A : Type) → F (F A) → F A

join-from : (A : Type) → Join (From A)
join-from A B f x = f x x

join-intointo : (B : Type) → Join (IntoInto B)
join-intointo B A nnnnx nx = nnnnx (munit-intointo B (A → B) nx)

