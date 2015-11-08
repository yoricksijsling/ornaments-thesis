module ContextFree.One.Examples.Nat where

open import ContextFree.One.Desc
open import ContextFree.One.Quoting
open import ContextFree.One.Quoted
open import ContextFree.One.Unquoting (quote Desc) (quote μ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
open import Data.Unit.Base
open import Data.Sum
open import Relation.Binary.PropositionalEquality

desc : Desc
desc = `1 `+ (`var `* `1) `+ `0

to : ℕ → μ desc
to zero = ⟨ inj₁ tt ⟩
to (suc n) = ⟨ inj₂ (inj₁ (to n , tt)) ⟩

from : μ desc → ℕ
from ⟨ inj₁ tt ⟩ = zero
from ⟨ inj₂ (inj₁ (n , tt)) ⟩ = suc (from n)
from ⟨ inj₂ (inj₂ ()) ⟩

to-from : ∀ x → from (to x) ≡ x
to-from zero = refl
to-from (suc x) = cong suc (to-from x)

from-to : ∀ x → to (from x) ≡ x
from-to ⟨ inj₁ tt ⟩ = refl
from-to ⟨ inj₂ (inj₁ n) ⟩ = cong (λ v → ⟨ inj₂ (inj₁ (v , tt)) ⟩) (from-to (proj₁ n))
from-to ⟨ inj₂ (inj₂ ()) ⟩

isContextFree-ℕ : IsContextFree ℕ
isContextFree-ℕ = record { desc = desc ; to = to ; from = from
                         ; to-from = to-from ; from-to = from-to }

qdt : SafeDatatype
qdt = quoteDatatype! (quote ℕ) 0

unquoteDecl qdesc = makeDesc qdt
unquoteDecl qto = makeTo (quote qdesc) qto qdt
unquoteDecl qfrom = makeFrom (quote qdesc) qfrom qdt

testDesc : qdesc ≡ desc
testDesc = refl

testTo : ∀ n → qto n ≡ to n
testTo zero = refl
testTo (suc n) = cong (λ v → ⟨ inj₂ (inj₁ (v , tt)) ⟩) (testTo n)

testFrom : ∀ n → qfrom n ≡ from n
testFrom ⟨ inj₁ tt ⟩ = refl
testFrom ⟨ inj₂ (inj₁ (n , tt)) ⟩ = cong suc (testFrom n)
testFrom ⟨ inj₂ (inj₂ ()) ⟩
