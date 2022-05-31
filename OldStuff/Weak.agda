{-# NO_POSITIVITY_CHECK #-}
data Weak : Set where
  <> : Weak
  <_-_> : Weak → Weak → Weak
  Fun : (Weak → Weak) → Weak

open Weak

data IsEmpty : Weak → Set where
  empty : IsEmpty <>

data IsList (El : Weak → Set) : Weak → Set where
  empty : IsList El <>
  list : {x xs : Weak} → El x → (IsList El xs) → IsList El (< x - xs >)

data IsListL (El : Weak → Set) : Weak → Set where
  empty : IsListL El <>
  list : {x xs : Weak} → El x → (IsListL El xs) → IsListL El (< xs - x >)

data IsPair (A B : Weak → Set) : Weak → Set where
  pair : {x y : Weak} → A x → B y → IsPair A B (< x - y >)

data IsTree (L : Weak → Set) : Weak → Set where
  leaf : {x : Weak} → L x → IsTree L x
  pair : {x y : Weak} → IsTree L x → IsTree L y → IsTree L (< x - y >)

data IsFun (A B : Weak → Set) : Weak → Set where
  fun : {f : Weak → Weak} → ({x : Weak} → A x → B (f x)) → IsFun A B (Fun f)


IsNat : Weak → Set
IsNat = IsList IsEmpty

IsData : Weak → Set
IsData = IsTree IsEmpty

record Elem (Pred : Weak → Set) : Set where
  constructor _[_]
  field
    val : Weak
    prf : Pred val

apply : {A B : Weak → Set} → Elem (IsFun A B) → Elem A → Elem B
apply (.(Fun f) [ fun {f} yp ]) (x [ xp ]) = f x [ yp xp ]

mapInner : (Weak → Weak) → (Weak → Weak)
mapInner f <> = <>
mapInner f (< x - xs >) = < f x - mapInner f xs >
mapInner f (Fun g) = Fun g

mapDef : Weak → Weak → Weak
mapDef (Fun f) x = mapInner f x
mapDef _ x = x

mapDef′ : Weak → Weak
mapDef′ f = Fun (mapDef f)

mapGivesList : {A B : Weak → Set} → {f xs : Weak} →
  IsFun A B f → IsList A xs → IsList B (mapDef f xs)
mapGivesList (fun _) empty = empty
mapGivesList fprf@(fun yprf) (list xprf xsprf) =
  list (yprf xprf) (mapGivesList fprf xsprf)

map : Weak
map = Fun mapDef′

mapIsFun : {A B : Weak → Set} →
  IsFun (IsFun A B) (IsFun (IsList A) (IsList B)) map
mapIsFun = fun (λ fprf → fun (mapGivesList fprf))

