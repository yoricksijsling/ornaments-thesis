module ContextFree.One.Examples.Unit where

open import ContextFree.One.Desc
open import ContextFree.One.Quoting
open import Data.Error
open import Data.Unit.Base
open import Data.Sum
open import Relation.Binary.PropositionalEquality

data Unit : Set where
  u : Unit

isContextFree-Unit : IsContextFree Unit
isContextFree-Unit = record { desc = desc ; to = to ; from = from
                            ; to-from = to-from ; from-to = from-to }
  where
  desc : Desc
  desc = `1
  to : Unit → μ desc
  to u = ⟨ tt ⟩
  from : μ desc → Unit
  from ⟨ tt ⟩ = u
  to-from : ∀ x → from (to x) ≡ x
  to-from u = refl
  from-to : ∀ x → to (from x) ≡ x
  from-to ⟨ tt ⟩ = refl


open IsContextFree isContextFree-Unit

testDesc : unquote (quoteDesc! (quote Unit)) ≡ desc
testDesc = refl

