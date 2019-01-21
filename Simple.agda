open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool)
open import Data.Vec

open import Untyped

data Type (n : ℕ) : Set where
  Var : Fin n → Type n
  _i->_ : Type n → Type n → Type n

data OpenDerivation {ps ts : ℕ} (pts : Vec (Type ts) ps) : OpenTerm ps → Type
    ts → Set where
  Apply : ∀ (f x : OpenTerm ps) (xt ot : Type ts) →
    (fd : OpenDerivation pts f (xt Type.i-> ot)) →
    (xd : OpenDerivation pts x xt) → OpenDerivation pts (OpenTerm.Apply f x) ot
  Lambda : ∀ (b : OpenTerm (ℕ.suc ps)) (xt ot : Type ts) →
    (bd : OpenDerivation (xt ∷ pts) b ot) →
    OpenDerivation pts (OpenTerm.Lambda b) (xt Type.i-> ot)
  Var : ∀ (var : Fin ps) →
    OpenDerivation pts (OpenTerm.Var var) (lookup var pts)

_i:_ : {n : ℕ} → Term → Type n → Set
x i: t = OpenDerivation Vec.[] x t

record ofType {n : ℕ} (ty : Type n) : Set where
  val : Untyped.Term
  proof : val i: ty

a : {n : ℕ} → Type (ℕ.suc n)
a = Type.Var Fin.zero

chBool : Type 1
chBool = a Type.i-> (a Type.i-> a)

toBool : ofType chBool → Bool
toBool b = ?
