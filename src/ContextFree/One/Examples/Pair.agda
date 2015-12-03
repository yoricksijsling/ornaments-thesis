module ContextFree.One.Examples.Pair where

open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.Unquoting (quote Desc) (quote μ) (quote RawIsContextFree)
open import ContextFree.One.Quoted
open import ContextFree.One.Quoting
open import Data.Fin using (#_)
open import Data.Product
open import Data.Sum
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

data Pair (A B : Set) : Set where
  pair : (a : A) → (b : B) → Pair A B

desc : (A B : Set) → Desc
desc A B = `P₀ A `* `P₀ B `* `1 `+ `0

pattern α a b = pair a b
pattern β a b = ⟨ inj₁ (a , b , tt) ⟩
pattern absurd-β = ⟨ inj₂ () ⟩

to : (A B : Set) → Pair A B → μ (desc A B)
to A B (α a b) = β a b

from : (A B : Set) → μ (desc A B) → Pair A B
from A B (β a b) = α a b
from A B absurd-β

to-from : (A B : Set) → ∀ x → from A B (to A B x) ≡ x
to-from A B (α a b) = refl

from-to : (A B : Set) → ∀ x → to A B (from A B x) ≡ x
from-to A B (β a b) = refl
from-to A B absurd-β

isContextFree-Pair : ∀ A B → IsContextFree (Pair A B)
isContextFree-Pair A B = record { desc = desc A B ; to = to A B ; from = from A B
                                ; to-from = to-from A B ; from-to = from-to A B }

qdt : NamedSafeDatatype
qdt = quoteDatatype! (quote Pair) 2

module TestQdt where
  open import Reflection
  open import Data.List
  testQdt : NamedSafeDatatype.sop qdt ≡ (quote pair , Spar (# 1) ∷ Spar (# 0) ∷ []) ∷
                                        []
  testQdt = refl

qdesc : DescFun (proj₁ (unnameSafeDatatype qdt))
qdesc = descFun (proj₁ (unnameSafeDatatype qdt))
unquoteDecl qto = makeTo qto (quote qdesc) qdt
unquoteDecl qfrom = makeFrom qfrom (quote qdesc) qdt
unquoteDecl qcf = makeRecord (quote qdesc) (quote qto) (quote qfrom) qdt

testDesc : ∀{A B} → qdesc A B ≡ desc A B
testDesc = refl

testTo : ∀{A B} x → qto A B x ≡ to A B x
testTo (α a b) = refl

testFrom : ∀{A B} x → qfrom A B x ≡ from A B x
testFrom (β a b) = refl
testFrom absurd-β
