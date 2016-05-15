
module Thesis.Named where

open import Common hiding (Vec)
open import Reflection
open import Cx.HasDesc

data Vec (A : Set) : Nat → Set where
  nil : Vec A 0
  cons : ∀ n → (x : A) → (xs : Vec A n) → Vec A (suc n)

unquoteDecl quotedVec vecHasDesc =
  deriveHasDesc quotedVec vecHasDesc (quote Vec)

vecDesc : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
vecDesc = QuotedDesc.desc quotedVec

quotedVec′ : QuotedDesc
quotedVec′ = quotedVec

vecHasDesc′ : {A : Set} {n : Nat} → HasDesc (Vec A n)
vecHasDesc′ = vecHasDesc

vecto : ∀{A n} → Vec A n → μ vecDesc (tt , A) (tt , n)
vecto = to
vecfrom : ∀{A n} → μ vecDesc (tt , A) (tt , n) → Vec A n
vecfrom = from
