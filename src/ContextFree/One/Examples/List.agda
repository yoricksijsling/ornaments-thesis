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

desc : (A : Set) → Desc
desc A = `1 `+ (`K A `* `var `* `1) `+ `0

to : (A : Set) → ListP A → μ (desc A)
to A [] = ⟨ inj₁ tt ⟩
to A (x ∷ xs) = ⟨ inj₂ (inj₁ (x , to A xs , tt)) ⟩

from : (A : Set) → μ (desc A) → ListP A
from A ⟨ inj₁ tt ⟩ = []
from A ⟨ inj₂ (inj₁ (x , xs , tt)) ⟩ = x ∷ from A xs
from A ⟨ inj₂ (inj₂ ()) ⟩

to-from : (A : Set) → ∀ x → from A (to A x) ≡ x
to-from A [] = refl
to-from A (x ∷ xs) = cong (_∷_ x) (to-from A xs)

from-to : (A : Set) → ∀ x → to A (from A x) ≡ x
from-to A ⟨ inj₁ tt ⟩ = refl
from-to A ⟨ inj₂ (inj₁ (x , xs , tt)) ⟩ = cong (λ v → ⟨ inj₂ (inj₁ (x , v , tt)) ⟩) (from-to A xs)
from-to A ⟨ inj₂ (inj₂ ()) ⟩

isContextFree-ListP : ∀ A → IsContextFree (ListP A)
isContextFree-ListP A = record { desc = desc A ; to = to A ; from = from A
                               ; to-from = to-from A ; from-to = from-to A }

qdt : SafeDatatype
qdt = quoteDatatype! (quote ListP) 1

unquoteDecl qdesc = makeDesc qdt
unquoteDecl qto = makeTo (quote qdesc) qto qdt

testDesc : ∀{A} → qdesc A ≡ desc A
testDesc = refl

testTo : ∀{A} xs → qto A xs ≡ to A xs
testTo [] = refl
testTo (x ∷ xs) = cong (λ v → ⟨ inj₂ (inj₁ (x , v , tt)) ⟩) (testTo xs)
