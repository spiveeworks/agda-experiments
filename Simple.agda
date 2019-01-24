open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool)
open import Data.Vec

open import Untyped

open import EqProps using (_<++_++>_)

data Type (n : ℕ) : Set where
  Var : Fin n → Type n
  _i->_ : Type n → Type n → Type n

data OpenDerivation {ps ts : ℕ} (pts : Vec (Type ts) ps) : OpenTerm ps → Type
    ts → Set where
  Apply : ∀ (xt ot : Type ts) →
    (f : OpenTerm ps) (fd : OpenDerivation pts f (xt Type.i-> ot)) →
    (x : OpenTerm ps) (xd : OpenDerivation pts x xt) →
    OpenDerivation pts (OpenTerm.Apply f x) ot
  Lambda : ∀ (xt ot : Type ts) →
    (b : OpenTerm (ℕ.suc ps)) (bd : OpenDerivation (xt ∷ pts) b ot) →
    OpenDerivation pts (OpenTerm.Lambda b) (xt Type.i-> ot)
  Var : ∀ (var : Fin ps) →
    OpenDerivation pts (OpenTerm.Var var) (lookup var pts)

_i:_ : {n : ℕ} → Term → Type n → Set
x i: t = OpenDerivation Vec.[] x t

a : {n : ℕ} → Type (ℕ.suc n)
a = Type.Var Fin.zero

chBool : Type 1
chBool = a Type.i-> (a Type.i-> a)

toBool : (term : Term) (proof : term i: chBool) → Bool
toBool t p = Bool.false

resp-substvars : {ts eps ps : ℕ} → (valt : Type ts) →
  (pts : Vec (Type ts) ps) → (epts : Vec (Type ts) eps) →
  (val : OpenTerm ps) → OpenDerivation pts val valt →
  ∀ (var : Fin (ℕ.suc (eps + ps))) →
  OpenDerivation
    (epts ++ pts)
    (lookup var (substvars val))
    (lookup var (epts <++ valt ++> pts))
resp-substvars valt pts epts val valprf var = ?

resp-subst : {ts eps ps : ℕ} → ∀(bt valt : Type ts) →
  (pts : Vec (Type ts) ps) → (epts : Vec (Type ts) eps) →
  (b : OpenTerm (ℕ.suc eps + ps)) → OpenDerivation (epts <++ valt ++> pts) b bt →
  (val : OpenTerm ps) → OpenDerivation pts val valt →
  OpenDerivation (epts ++ pts) (subst b val) bt
-- thank you proof automation
resp-subst bt valt pts epts (Apply f x) (Apply xt _ _ fprf _ xprf) val valprf =
  Apply xt bt
    (subst f val) (resp-subst (xt i-> bt) valt pts epts f fprf val valprf)
    (subst x val) (resp-subst xt valt pts epts x xprf val valprf)
resp-subst .(xt i-> bt) valt pts epts (Lambda b) (Lambda xt bt .b bprf) val valprf =
  Lambda xt bt (subst b val) (resp-subst bt valt pts (xt ∷ epts) b bprf val valprf) where
resp-subst .(lookup v (epts <++ valt ++> pts)) valt pts epts (Var v) (Var .v) val valprf =
  resp-substvars valt pts epts val valprf v

resp-subst′ : {ts ps : ℕ} → ∀(t : Type ts) → (b : OpenTerm (ℕ.suc ps)) →
  (x : OpenTerm ps) → (pts : Vec (Type ts) ps) →
  OpenDerivation pts (Apply (Lambda b) x) t →
  OpenDerivation pts (subst b x) t
resp-subst′ t b x pts (Apply xt .t .(Lambda b) (Lambda .xt .t .b bprf) .x xprf)
  = resp-subst t xt pts [] b bprf x xprf

