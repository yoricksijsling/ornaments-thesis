module ContextFree.One.Examples.Unit where

open import ContextFree.One.Desc
open import ContextFree.One.Quoting
open import ContextFree.One.Quoted
open import ContextFree.One.Unquoting (quote Desc) (quote μ)
open import Data.Error
open import Data.Unit.Base
open import Data.Sum
open import Relation.Binary.PropositionalEquality

data Unit : Set where
  u : Unit

desc : Desc
desc = `1 `+ `0

to : Unit → μ desc
to u = ⟨ inj₁ tt ⟩

from : μ desc → Unit
from ⟨ inj₁ tt ⟩ = u
from ⟨ inj₂ () ⟩

to-from : ∀ x → from (to x) ≡ x
to-from u = refl

from-to : ∀ x → to (from x) ≡ x
from-to ⟨ inj₁ tt ⟩ = refl
from-to ⟨ inj₂ () ⟩

isContextFree-Unit : IsContextFree Unit
isContextFree-Unit = record { desc = desc ; to = to ; from = from
                            ; to-from = to-from ; from-to = from-to }

qdt : SafeDatatype
qdt = quoteDatatype! (quote Unit) 0

unquoteDecl qdesc = makeDesc qdt
unquoteDecl qto = makeTo (quote qdesc) qto qdt
unquoteDecl qfrom = makeFrom (quote qdesc) qfrom qdt

testDesc : qdesc ≡ desc
testDesc = refl

testTo : ∀ x → qto x ≡ to x
testTo u = refl

testFrom : ∀ x → qfrom x ≡ from x
testFrom ⟨ inj₁ tt ⟩ = refl
testFrom ⟨ inj₂ () ⟩
