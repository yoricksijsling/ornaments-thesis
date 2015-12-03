module ContextFree.One.Examples.Unit where

open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.Unquoting (quote Desc) (quote μ) (quote RawIsContextFree)
open import ContextFree.One.Quoted
open import ContextFree.One.Quoting
open import Data.Error
open import Data.Product using (proj₁)
open import Data.Sum
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

data Unit : Set where
  u : Unit

desc : Desc
desc = `1 `+ `0

pattern α = u
pattern β = ⟨ inj₁ tt ⟩
pattern absurd-β = ⟨ inj₂ () ⟩

to : Unit → μ desc
to α = β

from : μ desc → Unit
from β = α
from absurd-β

to-from : ∀ x → from (to x) ≡ x
to-from α = refl

from-to : ∀ x → to (from x) ≡ x
from-to β = refl
from-to absurd-β

isContextFree-Unit : IsContextFree Unit
isContextFree-Unit = record { desc = desc ; to = to ; from = from
                            ; to-from = to-from ; from-to = from-to }

qdt : NamedSafeDatatype
qdt = quoteDatatype! (quote Unit) 0

module TestQdt where
  open import Reflection
  open import Data.List
  open import Data.Product
  testQdt : NamedSafeDatatype.sop qdt ≡ (quote u , []) ∷ []
  testQdt = refl

qdesc : DescFun (proj₁ (unnameSafeDatatype qdt))
qdesc = descFun (proj₁ (unnameSafeDatatype qdt))
unquoteDecl qto = makeTo qto (quote qdesc) qdt
unquoteDecl qfrom = makeFrom qfrom (quote qdesc) qdt
unquoteDecl qcf = makeRecord (quote qdesc) (quote qto) (quote qfrom) qdt

testDesc : qdesc ≡ desc
testDesc = refl

testTo : ∀ x → qto x ≡ to x
testTo α = refl

testFrom : ∀ x → qfrom x ≡ from x
testFrom β = refl
testFrom absurd-β
