module ContextFree.One.Examples.List where

open import ContextFree.One.Desc
open import ContextFree.One.Quoting
open import ContextFree.One.Quoted
open import ContextFree.One.Unquoting (quote Desc) (quote μ)
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
  desc = `1 `+ (`K A `* `var `* `1) `+ `0
  to : ListP A → μ desc
  to [] = ⟨ inj₁ tt ⟩
  to (x ∷ xs) = ⟨ inj₂ (inj₁ (x , to xs , tt)) ⟩
  from : μ desc → ListP A
  from ⟨ inj₁ tt ⟩ = []
  from ⟨ inj₂ (inj₁ (x , xs , tt)) ⟩ = x ∷ from xs
  from ⟨ inj₂ (inj₂ ()) ⟩
  to-from : ∀ x → from (to x) ≡ x
  to-from [] = refl
  to-from (x ∷ xs) = cong (_∷_ x) (to-from xs)
  from-to : ∀ x → to (from x) ≡ x
  from-to ⟨ inj₁ tt ⟩ = refl
  from-to ⟨ inj₂ (inj₁ (x , xs , tt)) ⟩ = cong (λ v → ⟨ inj₂ (inj₁ (x , v , tt)) ⟩) (from-to xs)
  from-to ⟨ inj₂ (inj₂ ()) ⟩

open module Foo (A : Set) = IsContextFree (isContextFree-ListP A)

qdt : SafeDatatype
qdt = quoteDatatype! (quote ListP) 1

unquoteDecl qdesc = makeDesc qdt
unquoteDecl qto = makeTo (quote qdesc) qto qdt

testDesc : ∀{A} → qdesc A ≡ desc A
testDesc = refl

testTo : ∀{A} xs → qto A xs ≡ to A xs
testTo [] = refl
testTo (x ∷ xs) = cong (λ v → ⟨ inj₂ (inj₁ (x , v , tt)) ⟩) (testTo xs)
