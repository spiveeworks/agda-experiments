-- Category typeclasses without actual typeclasses
module Category where

{-
record Category1 (Obj : Set1) (Morph : Obj -> Obj -> Set) : Set1 where
  field
    id : (x : Obj) -> Morph x x
    compose : (x y z : Obj) -> Morph y z -> Morph x y -> Morph x z

ExpCat : Category1 Set (\A B -> (A -> B))
Category1.id PiCat A x = x
Category1.compose PiCat A B C f g x = f (g x)
-}


record Functor (F : Set -> Set) : Set1 where
  field
    map : {a : Set} -> (a -> a) -> (F a -> F a)

record Monad (F : Set -> Set) : Set1 where
  field
    functor : Functor F
    unit : {a : Set} -> a -> F a
    counit : {a : Set} -> F (F a) -> F a


