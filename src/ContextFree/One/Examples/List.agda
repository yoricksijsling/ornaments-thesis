module ContextFree.One.Examples.List where

open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.Unquoting (quote Desc) (quote μ) (quote RawIsContextFree)
open import ContextFree.One.Quoted
open import ContextFree.One.Quoting
open import Data.Fin using (#_)
open import Data.Unit.Base
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

infixr 5 _∷_

data ListP (A : Set) : Set where
  [] : ListP A
  _∷_ : A → ListP A → ListP A

desc : (A : Set) → Desc
desc A = `1 `+ (`P₀ A `* `rec `* `1) `+ `0

pattern nil-α = []
pattern nil-β = ⟨ inj₁ tt ⟩
pattern cons-α x xs = x ∷ xs
pattern cons-β x xs = ⟨ inj₂ (inj₁ (x , xs , tt)) ⟩
pattern absurd-β = ⟨ inj₂ (inj₂ ()) ⟩

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
qdt = quoteDatatype! (quote ListP) 1

module TestQdt where
  open import Reflection
  open import Data.List
  testQdt : NamedSafeDatatype.sop qdt ≡ (quote ListP.[]  , []) ∷
                                        (quote ListP._∷_ , Spar (# 0) ∷ Srec ∷ []) ∷
                                        []
  testQdt = refl

qdesc : DescFun (proj₁ (unnameSafeDatatype qdt))
qdesc = descFun (proj₁ (unnameSafeDatatype qdt))
unquoteDecl qto = makeTo qto (quote qdesc) qdt
unquoteDecl qfrom = makeFrom qfrom (quote qdesc) qdt
unquoteDecl qcf = makeRecord (quote qdesc) (quote qto) (quote qfrom) qdt

testDesc : ∀{A} → qdesc A ≡ desc A
testDesc = refl

testTo : ∀{A} xs → qto A xs ≡ to A xs
testTo nil-α = refl
testTo (cons-α x xs) = cong (cons-β x) (testTo xs)

testFrom : ∀{A} xs → qfrom A xs ≡ from A xs
testFrom nil-β = refl
testFrom (cons-β x xs) = cong (cons-α x) (testFrom xs)
testFrom absurd-β
