module ContextFree.One.Examples.Nat where

open import Common
open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.Unquoting
open import ContextFree.One.Quoted
open import ContextFree.One.Quoting

desc : Desc
desc = `1 `+ (`var `* `1) `+ `0

pattern zero-α = zero
pattern zero-β = ⟨ left tt ⟩
pattern suc-α n = suc n
pattern suc-β n = ⟨ right (left (n , tt)) ⟩
pattern absurd-β = ⟨ right (right ()) ⟩

to : Nat → μ desc
to zero-α = zero-β
to (suc-α n) = suc-β (to n)

from : μ desc → Nat
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

isContextFree-Nat : IsContextFree Nat
isContextFree-Nat = record { desc = desc ; to = to ; from = from
                         ; to-from = to-from ; from-to = from-to }

qdt : NamedSafeDatatype
qdt = quoteDatatypeᵐ Nat

module TestQdt where
  open import Builtin.Reflection
  open import ContextFree.One.Params
  test-qdt : qdt ≡ mk (quote Nat) 0 []
                      ((quote Nat.zero , []) ∷
                       (quote Nat.suc , Srec ∷ []) ∷
                       [])
  test-qdt = refl

unquoteDecl qrec = defineRecord qrec qdt

module Q = RawIsContextFree qrec

testDesc : Q.desc ≡ desc
testDesc = refl

testTo : ∀ n → Q.to n ≡ to n
testTo zero-α = refl
testTo (suc-α n) = cong suc-β (testTo n)

testFrom : ∀ n → Q.from n ≡ from n
testFrom zero-β = refl
testFrom (suc-β n) = cong suc-α (testFrom n)
testFrom absurd-β
