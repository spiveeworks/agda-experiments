module Models.Testing where

open import Models.SimplyTyped

a : Type {2}
a = var fzero

b : Type {2}
b = var (fsuc fzero)

const-ty = a [→] b [→] a
const-expr : Expr {2} 0
const-expr = Lambda a (Lambda b (Var (fsuc fzero)))

const-derivation : given [] expr const-expr has-type const-ty
const-derivation = Typechecks.derivation (Dec.proof (type-check [] const-expr))

const : ∀ {A B : Set} → A → B → A
const {A} {B} = to-function [] const-expr const-ty const-derivation (A :: B :: []) cempty

const-proof : ∀ {A B : Set} → _≡_ {2} {A → B → A} (λ x y → const {A} {B} x y) (λ x y → x)
const-proof = refl
