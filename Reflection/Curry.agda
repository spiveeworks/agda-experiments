module Reflection.Curry where
open import Data.Nat as ℕ using (ℕ)
open import Data.Vec as Vec using (Vec)

OpType : ℕ → (A B : Set) → Set
OpType 0 A B = B
OpType (ℕ.suc n) A B = A → OpType n A B

associateOpIn : {n : ℕ} {A B : Set} → (A → OpType n A B) → OpType n A (A → B)
associateOpIn {0} f = f
associateOpIn {ℕ.suc n} f x = associateOpIn (f x)

associateOpOut : {n : ℕ} {A B : Set} → (OpType n A (A → B)) → A → OpType n A B
associateOpOut {0} f x = f x
associateOpOut {ℕ.suc n} f x = associateOpOut (f x)

composeOp : {n : ℕ} {A B C : Set} → (B → C) → OpType n A B → OpType n A C
composeOp {0} f x = f x
composeOp {ℕ.suc n} f g x = composeOp {n} f (g x)

uncurryOp₁ : {n m : ℕ} {A B : Set} → (A → OpType n A (Vec A m → B)) →
  OpType n A (Vec A (ℕ.suc m) → B)
uncurryOp₁ {n} f =
  composeOp {n} (λ {f (x Vec.∷ xs) → f x xs}) (associateOpIn f)

curryOp₁ : {n m : ℕ} {A B : Set} → (OpType n A (Vec A (ℕ.suc m) → B)) →
  A → OpType n A (Vec A m → B)
curryOp₁ {n} f =
  associateOpOut (composeOp {n} (λ f x xs → f (x Vec.∷ xs)) f)

right-ident : ∀ n (C : ℕ → Set) → C (n ℕ.+ 0) → C n
right-ident 0 C z = z
right-ident (ℕ.suc n) C z = right-ident n (λ m → C (ℕ.suc m)) z

comm-succ : ∀ n m (C : ℕ → Set) → C (n ℕ.+ ℕ.suc m) → C (ℕ.suc n ℕ.+ m)
comm-succ 0 m C z = z
comm-succ (ℕ.suc n) m C z = comm-succ n m (λ nm → C (ℕ.suc nm)) z

curryOpHelper : {n m : ℕ} {A B : Set} →
  OpType n A (Vec A m → B) → OpType (m ℕ.+ n) A B
curryOpHelper {n} {ℕ.zero} f = composeOp {n} (λ f → f Vec.[]) f
curryOpHelper {n} {ℕ.suc m} {A} {B} f = comm-succ m n (λ mn → OpType mn A B)
  (curryOpHelper {ℕ.suc n} {m} {A} {B}
  (curryOp₁ {n} {m} {A} {B} f))

curryOp : {n : ℕ} {A B : Set} → (Vec A n → B) → OpType n A B
curryOp {n} {A} {B} f =
  right-ident n (λ m → OpType m A B) (curryOpHelper {0} {n} f)

