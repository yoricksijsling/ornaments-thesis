module ContextFree.One.Examples.Nat where

open import ContextFree.One.Desc
open import ContextFree.One.Quoting
open import Data.Nat
open import Data.Product
open import Data.Unit.Base
open import Data.Sum
open import Relation.Binary.PropositionalEquality


isContextFree-ℕ : IsContextFree ℕ
isContextFree-ℕ = record { desc = desc ; to = to ; from = from
                         ; to-from = to-from ; from-to = from-to }
  where
  desc : Desc
  desc = `1 `+ `var
  to : ℕ → μ desc
  to zero = ⟨ inj₁ tt ⟩
  to (suc n) = ⟨ inj₂ (to n) ⟩
  from : μ desc → ℕ
  from ⟨ inj₁ tt ⟩ = zero
  from ⟨ inj₂ n ⟩ = suc (from n)
  to-from : ∀ x → from (to x) ≡ x
  to-from zero = refl
  to-from (suc x) = cong suc (to-from x)
  from-to : ∀ x → to (from x) ≡ x
  from-to ⟨ inj₁ tt ⟩ = refl
  from-to ⟨ inj₂ n ⟩ = cong (λ v → ⟨ inj₂ v ⟩) (from-to n)

open IsContextFree isContextFree-ℕ

testDesc : unquote (quoteDesc! (quote ℕ) 0) ≡ desc
testDesc = refl

