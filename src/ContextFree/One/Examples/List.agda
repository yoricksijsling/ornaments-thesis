module ContextFree.One.Examples.List where

open import Common
open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.Unquoting
open import ContextFree.One.Quoted
open import ContextFree.One.Quoting

infixr 5 _∷_

data ListP (A : Set) : Set where
  [] : ListP A
  _∷_ : A → ListP A → ListP A

desc : (A : Set) → Desc
desc A = `1 `+ (`P₀ A `* `var `* `1) `+ `0

pattern nil-α = []
pattern nil-β = ⟨ left tt ⟩
pattern cons-α x xs = x ∷ xs
pattern cons-β x xs = ⟨ right (left (x , xs , tt)) ⟩
pattern absurd-β = ⟨ right (right ()) ⟩

to : (A : Set) → ListP A → μ (desc A)
to A nil-α = nil-β
to A (cons-α x xs) = cons-β x (to A xs)

from : (A : Set) → μ (desc A) → ListP A
from A nil-β = []
from A (cons-β x xs) = cons-α x (from A xs)
from A absurd-β

to-from : (A : Set) → ∀ x → from A (to A x) ≡ x
to-from A nil-α = refl
to-from A (cons-α x xs) = cong (λ xs′ → cons-α x xs′) (to-from A xs)

from-to : (A : Set) → ∀ x → to A (from A x) ≡ x
from-to A nil-β = refl
from-to A (cons-β x xs) = cong (λ xs′ → cons-β x xs′) (from-to A xs)
from-to A absurd-β

isContextFree-ListP : ∀ A → IsContextFree (ListP A)
isContextFree-ListP A = record { desc = desc A ; to = to A ; from = from A
                               ; to-from = to-from A ; from-to = from-to A }

qdt : NamedSafeDatatype
qdt = quoteDatatypeᵐ ListP

module TestQdt where
  open import Builtin.Reflection
  open import ContextFree.One.Params
  test-qdt : qdt ≡ mk (quote ListP) 1 (param₀ visible "A" ∷ [])
                      ((quote ListP.[]  , []) ∷
                       (quote ListP._∷_ , Spar 0 ∷ Srec ∷ []) ∷
                       [])
  test-qdt = refl

unquoteDecl qrec = defineRecord qrec qdt

module Q (A : Set) = RawIsContextFree (qrec A)

testDesc : ∀{A} → Q.desc A ≡ desc A
testDesc = refl

testTo : ∀{A} xs → Q.to A xs ≡ to A xs
testTo nil-α = refl
testTo (cons-α x xs) = cong (cons-β x) (testTo xs)

testFrom : ∀{A} xs → Q.from A xs ≡ from A xs
testFrom nil-β = refl
testFrom (cons-β x xs) = cong (cons-α x) (testFrom xs)
testFrom absurd-β
