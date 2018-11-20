open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as HetEq


extensionalEq : {A B : Set} → (f g : A → B) → (p : (x : A) → f x ≡ g x) →
    HetEq._≅_ (λ x → p x)  (λ x → refl {_} {B} {f x})
extensionalEq f g p = refl
