-- Category typeclasses without actual typeclasses
module Category where

record Category (Obj: Set) (Morph: Obj -> Obj -> Set) : Set where
  field
	id: (x: Obj) -> Morph x x
	compose: (x y z: Obj) -> Morph y z -> Morph x y -> Morph x z

PiCat: Category Type (\A B -> (A -> B))
PiCat.id A x = x
PiCat.compose A B C f g = f . g
