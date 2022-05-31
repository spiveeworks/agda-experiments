open import Relation.Binary.PropositionalEquality
open import Category.Monad
open import Category.Monad.Indexed using (RawIMonad)

substIrr : {A : Set} {x y : A} (P : A → Set) → (x ≡ y) → P x → P y
substIrr P refl p = p

.irrfun : {A : Set} -> A -> A
irrfun x = x

--irrap : {A : Set} -> .(A -> A) -> A -> A
--irrap f x = f x

irrcon : {A : Set} {B : .A → Set} {C : .(x : A) → .(B x) -> Set} →
  (.(x : A) → .(y : B x) → C x y) → .(f : (x : A) → B x) → .(x : A) → C x (f x)
irrcon con f x = con x (f x)

irrcon′ : {A B C : Set} → (.B → C) → .(A → B) → .A → C
irrcon′ con f x = con (f x)

record Irr (A : Set) : Set where
  constructor irr
  field
    .proof : A

instance
  MonadIrr : RawMonad Irr
  RawIMonad.return MonadIrr = irr
  RawIMonad._>>=_ MonadIrr dotx f = irr (Irr.proof (f (Irr.proof dotx)))
