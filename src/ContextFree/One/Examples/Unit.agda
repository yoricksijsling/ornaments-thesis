module ContextFree.One.Examples.Unit where

open import Common
open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.EmbeddingProjection
open import ContextFree.One.Quoted
open import ContextFree.One.Quoting

data U : Set where
  u : U

desc : Desc
desc = `1 `+ `0

pattern α = u
pattern β = ⟨ left tt ⟩
pattern absurd-β = ⟨ right () ⟩

to : U → μ desc
to α = β

from : μ desc → U
from β = α
from absurd-β

to-from : ∀ x → from (to x) ≡ x
to-from α = refl

from-to : ∀ x → to (from x) ≡ x
from-to β = refl
from-to absurd-β

isContextFree-U : IsContextFree U
isContextFree-U = record { desc = desc ; to = to ; from = from
                            ; to-from = to-from ; from-to = from-to }

qdt : NamedSafeDatatype
qdt = quoteDatatypeᵐ U

module TestQdt where
  open import Builtin.Reflection
  open import ContextFree.One.Params
  testQdt : qdt ≡ mk (quote U) 0 [] ((quote u , []) ∷ [])
  testQdt = refl

unquoteDecl qrec = defineRecord qrec qdt

module Q = RawIsContextFree qrec

testDesc : Q.desc ≡ desc
testDesc = refl

testTo : ∀ x → Q.to x ≡ to x
testTo α = refl

testFrom : ∀ x → Q.from x ≡ from x
testFrom β = refl
testFrom absurd-β
