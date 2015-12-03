module ContextFree.One.Examples.Nat where

open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.Unquoting (quote Desc) (quote μ) (quote RawIsContextFree)
open import ContextFree.One.Quoted
open import ContextFree.One.Quoting
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
open import Data.Unit.Base
open import Data.Sum
open import Relation.Binary.PropositionalEquality

desc : Desc
desc = `1 `+ (`var `* `1) `+ `0

pattern zero-α = zero
pattern zero-β = ⟨ inj₁ tt ⟩
pattern suc-α n = suc n
pattern suc-β n = ⟨ inj₂ (inj₁ (n , tt)) ⟩
pattern absurd-β = ⟨ inj₂ (inj₂ ()) ⟩

to : ℕ → μ desc
to zero = zero-β
to (suc n) = ⟨ inj₂ (inj₁ (to n , tt)) ⟩

from : μ desc → ℕ
from zero-β = zero-α
from (suc-β n) = suc-α (from n)
from absurd-β

to-from : ∀ x → from (to x) ≡ x
to-from zero-α = refl
to-from (suc-α n) = cong suc-α (to-from n)

from-to : ∀ x → to (from x) ≡ x
from-to zero-β = refl
from-to (suc-β n) = cong suc-β (from-to n)
from-to absurd-β

isContextFree-ℕ : IsContextFree ℕ
isContextFree-ℕ = record { desc = desc ; to = to ; from = from
                         ; to-from = to-from ; from-to = from-to }

qdt : NamedSafeDatatype
qdt = quoteDatatype! (quote ℕ) 0

qdesc : DescFun (proj₁ (unnameSafeDatatype qdt))
qdesc = descFun (proj₁ (unnameSafeDatatype qdt))
unquoteDecl qto = makeTo qto (quote qdesc) qdt
unquoteDecl qfrom = makeFrom qfrom (quote qdesc) qdt
unquoteDecl qcf = makeRecord (quote qdesc) (quote qto) (quote qfrom) qdt

module TestQdt where
  open import Reflection
  open import Data.List
  testQdt : NamedSafeDatatype.sop qdt ≡ (quote zero , []) ∷
                                         (quote suc , Srec ∷ []) ∷
                                         []
  testQdt = refl

testDesc : qdesc ≡ desc
testDesc = refl

testTo : ∀ n → qto n ≡ to n
testTo zero-α = refl
testTo (suc-α n) = cong suc-β (testTo n)

testFrom : ∀ n → qfrom n ≡ from n
testFrom zero-β = refl
testFrom (suc-β n) = cong suc-α (testFrom n)
testFrom absurd-β
