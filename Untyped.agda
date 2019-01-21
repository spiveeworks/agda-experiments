open import Data.Nat using (ℕ)
open import Data.Fin as Fin using (Fin)

data OpenTerm (n : ℕ) : Set where
  Apply : OpenTerm n → OpenTerm n → OpenTerm n
  Lambda : OpenTerm (ℕ.suc n) → OpenTerm n
  Var : Fin n → OpenTerm n

Term : Set
Term = OpenTerm ℕ.zero

