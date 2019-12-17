module Reflection.Expr where

-- blackboard ℕ makes it look like it is a subset of ℂ which is bugging me
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec using (Vec)
open import Data.Vec.Functional as Vector using (Vector)

record System : Set where
  constructor system
  field
    length : ℕ
    params : Vector ℕ length

record Operator (sys : System) (A : Set) : Set where
  constructor buildOp
  field
    id : Fin (System.length sys)
-- should this one be Vector as well?
    arguments : Vec A (System.params sys id)

record Expr (sys : System) : Set where
  inductive
  constructor fromOp
  field
    toOp : Operator sys (Expr sys)

{-
 - Variable Extensions
 -}

extend : System → ℕ → System
extend (system len rs) n = system (len ℕ.+ n) (rs Vector.++ (λ _ → 0))

_≡l_ : {A : Set} → A → A → Set₁
x ≡l y = (C : _ → Set) → C x → C y

open import Data.Sum as Sum using (_⊎_)

-- similar to Data.Fin.Properties.splitAt-inject+
splitAt-inject+ : ∀ m n i → Sum.inj₁ i ≡l Fin.splitAt m (Fin.inject+ n i)
splitAt-inject+ (ℕ.suc m) n Fin.zero C z = z
splitAt-inject+ (ℕ.suc m) n (Fin.suc i) C z =
  splitAt-inject+ m n i
-- I'm not sure leibniz equality was such a good idea after all
-- that said just because rewrite takes less characters doesnt mean it is
-- easier to read or write
  (λ j → C (Sum.[ (λ x → _⊎_.inj₁ (Fin.suc x)) , (λ x → _⊎_.inj₂ x) ] j)) z

-- similar to Data.Fin.Properties.splitAt-raise
splitAt-raise : ∀ m n i → Sum.inj₂ i ≡l Fin.splitAt m (Fin.raise {n} m i)
splitAt-raise ℕ.zero n i C z = z
splitAt-raise (ℕ.suc m) n i C z =
  splitAt-raise m n i
  (λ j → C (Sum.[ (λ x → _⊎_.inj₁ (Fin.suc x)) , (λ x → _⊎_.inj₂ x) ] j)) z

injectOp : {sys : System} {n : ℕ} {A : Set} →
  Operator sys A → Operator (extend sys n) A
injectOp {system len ops} {n} {A} (buildOp id args) =
  buildOp (Fin.inject+ n id)
  (splitAt-inject+ _ _ id (λ j → Vec A (Sum.[ ops , (λ _ → 0) ] j)) args)

{-# TERMINATING #-}
inject : {sys : System} → {n : ℕ} → Expr sys → Expr (extend sys n)
inject (fromOp (buildOp id args)) =
  fromOp (injectOp (buildOp id (Vec.map inject args)))

varOp : {sys : System} {n : ℕ} {A : Set} →
  Fin n → Operator (extend sys n) A
varOp {system len ops} {n} {A} i =
  buildOp (Fin.raise len i)
  (splitAt-raise _ _ i (λ j → Vec A (Sum.[ ops , (λ _ → 0) ] j)) Vec.[])

var : {sys : System} {n : ℕ} → Fin n → Expr (extend sys n)
var i = fromOp (varOp i)

{-
 - Substitution
 -}

Substitution : System → (A : Set) → Set
Substitution (system len ops) A = (i : Fin len) → (Vec A (ops i) → A)

{-# TERMINATING #-}
evaluate : (sys : System) → {A : Set} → Substitution sys A → Expr sys → A
evaluate sys subs (fromOp (buildOp id args)) =
  subs id (Vec.map (evaluate sys subs) args)

idSubst : (sys : System) → Substitution sys (Expr sys)
idSubst sys i args = fromOp (buildOp i args)

injectSubst : (sys : System) → ∀ n → Substitution sys (Expr (extend sys n))
injectSubst sys n i args = fromOp (injectOp (buildOp i args))

extendSubst : (sys : System) → ∀ {n} {A} →
  Substitution sys A → Vector A n → Substitution (extend sys n) A
extendSubst (system len ops) {n} base vals i = elim (Fin.splitAt len i) where
  elim : (i : Fin len ⊎ Fin n) → Vec _ (Sum.[ ops , (λ _ → 0) ] i) → _
  elim (Sum.inj₁ i) args = base i args
  elim (Sum.inj₂ j) Vec.[] = vals j

varSubst : (sys : System) → ∀ n m → Vector (Expr (extend sys m)) n →
  Substitution (extend sys n) (Expr (extend sys m))
varSubst sys n m = extendSubst sys (injectSubst sys m)

compose : {sys : System} → {n m : ℕ} →
  Expr (extend sys n) → Vector (Expr (extend sys m)) n →
  Expr (extend sys m)
compose {sys} {n} {m} f xs = evaluate (extend sys n) (varSubst sys n m xs) f

apply : {sys : System} → Expr (extend sys 1) → Expr sys → Expr sys
apply {sys} f x = evaluate (extend sys 1) (extendSubst sys (idSubst sys) (λ _ → x)) f
