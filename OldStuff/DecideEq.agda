open import Data.Bool
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

IsTrue : Bool -> Set
IsTrue true = ⊤
IsTrue false = ⊥

record DecideEqIntro (G : Set) : Set where
  field
    eqb : (a b : G) -> Bool
    refl : {a : G} -> IsTrue (eqb a a)

_==_ : {G : Set} {{eq : DecideEqIntro G}} -> G -> G -> Set
_==_ {G} {{eq}} a b = IsTrue (DecideEqIntro.eqb eq a b)

record DecideEq (G : Set) : Set1 where
  field
    {{eqIntro}} : DecideEqIntro G
    map : {a b : G} {G' : Set} {{eq' : DecideEqIntro G'}} (f : G -> G') ->
        a == b -> f a == f b

instance
  boolEqIntro : DecideEqIntro Bool
  DecideEqIntro.eqb boolEqIntro true true = true
  DecideEqIntro.eqb boolEqIntro false false = true
  DecideEqIntro.eqb boolEqIntro true false = false
  DecideEqIntro.eqb boolEqIntro false true = false

  DecideEqIntro.refl boolEqIntro {true} = tt
  DecideEqIntro.refl boolEqIntro {false} = tt

  boolEq : DecideEq Bool
  DecideEq.map boolEq {true} {true} {{eq'}} _ _ = DecideEqIntro.refl eq'
  DecideEq.map boolEq {false} {false} {{eq'}} _ _ = DecideEqIntro.refl eq'
  DecideEq.map boolEq {true} {false} _ ()
  DecideEq.map boolEq {false} {true} _ ()
