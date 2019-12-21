module Reflection.Equation where

open import Reflection.Expr

import RelExt
module EquivExt = RelExt.EquivExt
open EquivExt using (EquivExt)

open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.Vec.Functional as Vector using (Vector)
open import Relation.Binary as Rel using (Rel)

ExprRel : (sys : System) (vars : ℕ) → Set₁
ExprRel sys vars = Rel (Expr sys vars) _

record BasisEquation (sys : System) : Set where
  constructor _:≈_
  field
    {vars} : ℕ
    lhs : Expr sys vars
    rhs : Expr sys vars

data BasisRel (sys : System) (eq : BasisEquation sys) (vars : ℕ) :
  ExprRel sys vars where
  intro :
    (f : Hole sys vars) (xs : Vector (Expr sys vars) (BasisEquation.vars eq)) →
    BasisRel sys eq vars
      (fill f (compose (BasisEquation.lhs eq) xs))
      (fill f (compose (BasisEquation.rhs eq) xs))

basicCong : ∀ {sys eq n} f {x y} →
  BasisRel sys eq n x y → BasisRel sys eq n (fill f x) (fill f y)
basicCong {sys} {eq} {n} f (intro g xs) = subst₂ (BasisRel sys eq n)
  (concat-fill f g _) (concat-fill f g _) (intro (f ++ g) xs) where
  open import Relation.Binary.PropositionalEquality using (subst₂)
  open Reflection.Expr.Properties using (concat-fill)

record DerivationRaw {sys : System} {numLaws : ℕ}
  (laws : Vector (BasisEquation sys) numLaws)
  (vars : ℕ) (x y : Expr sys vars) : Set where
  constructor raw
  field
    i : Fin numLaws
    prf : BasisRel sys (laws i) vars x y

Derivation : {sys : System} {numLaws : ℕ} →
  Vector (BasisEquation sys) numLaws → (vars : ℕ) → ExprRel sys vars
Derivation laws vars = EquivExt (DerivationRaw laws vars)

law : ∀ {sys numLaws laws} i {n} xs → Derivation {sys} {numLaws} laws n
  (compose (BasisEquation.lhs (laws i)) xs)
  (compose (BasisEquation.rhs (laws i)) xs)
law i xs = EquivExt.inject (raw i (intro id xs))

cong : ∀ {sys numLaws laws vars} f {x y} →
  Derivation {sys} {numLaws} laws vars x y →
  Derivation {sys} {numLaws} laws vars (fill f x) (fill f y)
cong f = EquivExt.image (fill f) _ _
  (λ{x y (raw i prf) → raw i (basicCong f prf)}) _ _

refl : ∀ {sys numLaws laws vars} →
  Rel.Reflexive (Derivation {sys} {numLaws} laws vars)
refl = EquivExt.refl _

sym : ∀ {sys numLaws laws vars} →
  Rel.Symmetric (Derivation {sys} {numLaws} laws vars)
sym = EquivExt.sym _

trans : ∀ {sys numLaws laws vars} →
  Rel.Transitive (Derivation {sys} {numLaws} laws vars)
trans = EquivExt.trans _

