open import Data.Nat as Nat using (ℕ; _+_)
open import Data.Fin as Fin using (Fin; toℕ)
open import Data.List as List using (List; _∷_; [])
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

open import Function using (case_of_)

open import EqProps

data OpenTerm (n : ℕ) : Set where
  Apply : OpenTerm n → OpenTerm n → OpenTerm n
  Lambda : OpenTerm (ℕ.suc n) → OpenTerm n
  Var : Fin n → OpenTerm n

Term : Set
Term = OpenTerm ℕ.zero

raiseinj : (orig depth ignore : ℕ) →
  Fin (ignore + orig) → Fin (ignore + depth + orig)
raiseinj orig depth Nat.zero v = Fin.raise depth v
raiseinj orig depth (Nat.suc ignore) Fin.zero = Fin.zero
raiseinj orig depth (Nat.suc ignore) (Fin.suc v) =
  Fin.suc (raiseinj orig depth ignore v)

-- x is defined with v₀..v_n, but we want these to be labelled v_i..v_n+i
-- with new variables fitting from 0 to i-1
-- additionally inside lambdas we will have v₀..v_j-1, v_j..v_n+j
-- which we want to be called v₀..v_j-1, v_i+j..v_n+i+j
-- with new variables fitting from j to i+j-1
-- note its orig + depth simply because orig is 0 anyway
raise : {orig : ℕ} (depth ignore : ℕ) →
  OpenTerm (ignore + orig) → OpenTerm (ignore + depth + orig)
raise d ig (Apply f x) = Apply (raise d ig f) (raise d ig x)
raise d ig (Lambda b) = Lambda (raise d (ℕ.suc ig) b)
raise {orig} d ig (Var v) = Var (raiseinj orig d ig v)

data Ordering : Set where
  less : Ordering
  equal : Ordering
  greater : Ordering

compare : {n : ℕ} → ℕ → Fin n → Ordering
compare 0 (Fin.suc y) = less
compare 0 Fin.zero = equal
compare (ℕ.suc x) Fin.zero = greater
compare (ℕ.suc x) (Fin.suc y) = compare x y

-- [v₀,v₁..vi..v{n+i}] => [v₀..v{i-1},v{i+1}..v{n+i}]
-- which means v{i+j} needs to be renumbered as i+j-1
-- i are variables added since starting subst, 'ex'
-- n are variables originally in scope, 'orig'
substvar : {ex orig : ℕ} → Fin (ℕ.suc (ex + orig)) → OpenTerm orig →
  OpenTerm (ex + orig)
substvar {ex@0} Fin.zero val = raise ex 0 val  -- explicit equals with ex=0
substvar {0} (Fin.suc var) val = Var var  -- explicit less with ex=0
substvar {ex@(ℕ.suc ex′)} {orig} var val with compare ex var
... | less = Var (pred var) where
  pred : Fin (ℕ.suc (ex + orig)) → Fin (ex + orig)
  pred Fin.zero = Fin.zero
  pred (Fin.suc x) = x
... | equal = raise ex 0 val
... | greater = Var (reduce var) where
  reduce : {n : ℕ} → Fin (ℕ.suc (ℕ.suc n)) → Fin (ℕ.suc n)
  reduce Fin.zero = Fin.zero
  reduce {0} (Fin.suc _) = Fin.zero
  reduce {ℕ.suc n} (Fin.suc x) = Fin.suc (reduce x)

-- use resp-subst to follow this algorithm
-- i.e. think about why (Apply (Lambda b) x) has the same type as (subst b x)
-- the first thing is Lambda b : t₁ -> t₂, x : t₁, so subst b x : t₂
-- b is defined in the context of a variable v₀ : t₁, and is already of type t₂
-- our goal is to replace any `v₀ : t₁ |- F(v₀) : t₃' with
--  `x : t₁ |- F(x) : t₃'
subst : {orig ex : ℕ} → OpenTerm (ℕ.suc (ex + orig)) → OpenTerm orig →
  OpenTerm (ex + orig)
subst (Apply f x) val = Apply (subst f val) (subst x val)
-- a variable is prepended to the context, so i goes up by one
-- meaning we now want to replace v_{i+1} with x instead of v_i
subst (Lambda b) val = Lambda (subst b val)
subst (Var v) val = substvar v val


{-# TERMINATING #-}
whnf : Term → OpenTerm 1
whnf (Apply f term) = whnf (subst (whnf f) term)
whnf (Lambda term) = term
whnf (Var ())

module whnfTests where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  id : {n : ℕ} → OpenTerm n
  id = OpenTerm.Lambda (OpenTerm.Var Fin.zero)

  const : {n : ℕ} → OpenTerm n
  const = OpenTerm.Lambda (OpenTerm.Lambda (OpenTerm.Var (Fin.suc Fin.zero)))

  testOne : whnf (id) ≡ OpenTerm.Var Fin.zero
  testOne = refl

  testTwo : whnf (OpenTerm.Apply id id) ≡ OpenTerm.Var Fin.zero
  testTwo = refl

  testThree : whnf (OpenTerm.Apply const id) ≡ id
  testThree = refl

record HeadNormal : Set where
  constructor HNF
  field
    vars : ℕ
    head : Fin vars
    tail : List (OpenTerm vars)

buildBody : (x : HeadNormal) → OpenTerm (HeadNormal.vars x)
buildBody (HNF vars head tail) = List.foldl Apply (Var head) tail

wrapLambdas : {n : ℕ} → OpenTerm n → OpenTerm 0
wrapLambdas {0} x = x
wrapLambdas {ℕ.suc _} x = wrapLambdas (Lambda x)

fromHeadNormal : HeadNormal → OpenTerm 0
fromHeadNormal = wrapLambdas ∘ buildBody


{-# TERMINATING #-}
hnf : {vars : ℕ} → OpenTerm vars → List (OpenTerm vars) → HeadNormal
hnf (Lambda b) (x List.∷ xs) = hnf (subst b x) xs
hnf (Lambda b) [] = hnf b []
hnf (Apply f x) xs = hnf f (x List.∷ xs)
hnf {vars} (Var head) tail = HNF vars head tail



