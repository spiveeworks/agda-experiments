open import Data.Product hiding (map)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

record Group (G : Set) : Set1 where
  field
    _≟_ : Decidable {A = G} _≡_
    _*_ : G -> G -> G
    associative : ∀ (a b c : G) -> a * (b * c) ≡ (a * b) * c
    id : G
    identity : ∀ (a : G) -> a * id ≡ a
    inverse : ∀ (a : G) -> ∃[ a′ ] (a * a′ ≡ id)

open Group {{...}}

record Enumerable (G : Set) : Set where
  field
    size : ℕ
    elems : Vec G size
    unique : ∀ {a b : Fin size}
        -> (lookup a elems ≡ lookup b elems) -> a ≡ b
    ind : G -> Fin size
    index : ∀ {a : G} -> lookup (ind a) elems ≡ a

open Enumerable {{...}}

-- lemma : {G : Set} {{Enum : Enumerable G}} ->
--     ∀ {a : Fin (size)} -> ind (lookup a elems) ≡ a
-- lemma {G} {a} = unique {G} {_} {_} (index {G} {lookup a elems})

images : {G : Set} {{Grp : Group G}} {{Enum : Enumerable G}} ->
    G -> Vec G (size {{Enum}})
images x = map (_*_ x) elems

cayley : {G : Set} {{Grp : Group G}} {{Enum : Enumerable G}} ->
    G -> Vec (Fin (size {{Enum}})) (size {{Enum}})
cayley x = map ind (images x)
