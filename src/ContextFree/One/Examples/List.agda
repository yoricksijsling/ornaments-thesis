module ContextFree.One.Examples.List where

open import ContextFree.One.Desc
open import ContextFree.One.Quoting
-- open import Data.List
open import Data.Unit.Base
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

data ListP (A : Set) : Set where
  [] : ListP A
  _∷_ : A → ListP A → ListP A

isContextFree-ListP : ∀ A → IsContextFree (ListP A)
isContextFree-ListP A = record { desc = desc ; to = to ; from = from
                              ; to-from = to-from ; from-to = from-to }
  where
  desc : Desc
  desc = `1 `+ (`K A `* `var)
  to : ListP A → μ desc
  to [] = ⟨ inj₁ tt ⟩
  to (x ∷ xs) = ⟨ inj₂ (x , to xs) ⟩
  from : μ desc → ListP A
  from ⟨ inj₁ tt ⟩ = []
  from ⟨ inj₂ (x , xs) ⟩ = x ∷ from xs
  to-from : ∀ x → from (to x) ≡ x
  to-from [] = refl
  to-from (x ∷ xs) = cong (λ v → x ∷ v) (to-from xs)
  from-to : ∀ x → to (from x) ≡ x
  from-to ⟨ inj₁ tt ⟩ = refl
  from-to ⟨ inj₂ (x , xs) ⟩ = cong (λ v → ⟨ inj₂ (x , v) ⟩) (from-to xs)

open module Foo (A : Set) = IsContextFree (isContextFree-ListP A)

testDesc : ∀{A : Set}{Foo : Set} → unquote (quoteDesc! (quote ListP) 1) A ≡ desc A
testDesc = refl
