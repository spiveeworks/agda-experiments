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

basicEquation : {sys : System} {eq : BasisEquation sys} → BasisRel sys eq
  (BasisEquation.vars eq) (BasisEquation.lhs eq) (BasisEquation.rhs eq)
basicEquation {sys} {law@(x :≈ y)} = subst₂ (BasisRel sys law _)
  (compose-var x) (compose-var y) (intro id var) where
  open import Relation.Binary.PropositionalEquality using (subst₂)
  open Reflection.Expr.Properties using (compose-var)

record DerivationRaw {sys : System} {numLaws : ℕ}
  (laws : Vector (BasisEquation sys) numLaws)
  (vars : ℕ) (x y : Expr sys vars) : Set where
  field
    i : Fin numLaws
    prf : BasisRel sys (laws i) vars x y

Derivation : {sys : System} {numLaws : ℕ} →
  Vector (BasisEquation sys) numLaws → (vars : ℕ) → ExprRel sys vars
Derivation laws vars = EquivExt (DerivationRaw laws vars)

law : ∀ {sys numLaws laws} i → Derivation {sys} {numLaws} laws
  (BasisEquation.vars (laws i))
  (BasisEquation.lhs (laws i)) (BasisEquation.rhs (laws i))
law i = EquivExt.inject record {i = i; prf = basicEquation}

refl : ∀ {sys numLaws laws vars} →
  Rel.Reflexive (Derivation {sys} {numLaws} laws vars)
refl = EquivExt.refl _

sym : ∀ {sys numLaws laws vars} →
  Rel.Symmetric (Derivation {sys} {numLaws} laws vars)
sym = EquivExt.sym _

trans : ∀ {sys numLaws laws vars} →
  Rel.Transitive (Derivation {sys} {numLaws} laws vars)
trans = EquivExt.trans _

