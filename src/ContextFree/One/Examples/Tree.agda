module ContextFree.One.Examples.Tree where

open import Common
open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.Unquoting
open import ContextFree.One.Quoted
open import ContextFree.One.Quoting

data Tree (A : Set) : Set where
  leaf : Tree A
  node1 : A → Tree A → Tree A
  node2 : A → Tree A → Tree A → Tree A

desc : (A : Set) → Desc
desc A = `1 `+ (`P₀ A `* `var `* `1) `+ (`P₀ A `* `var `* `var `* `1) `+ `0

pattern leaf-α = leaf
pattern leaf-β = ⟨ left tt ⟩
pattern node1-α v xs = node1 v xs
pattern node1-β v xs = ⟨ right (left (v , xs , tt)) ⟩
pattern node2-α v xs ys = node2 v xs ys
pattern node2-β v xs ys = ⟨ right (right (left (v , xs , ys , tt))) ⟩
pattern absurd-β = ⟨ right (right (right ())) ⟩

to : (A : Set) → Tree A → μ (desc A)
to A leaf-α = leaf-β
to A (node1-α v xs) = node1-β v (to A xs)
to A (node2-α v xs ys) = node2-β v (to A xs) (to A ys)

from : (A : Set) → μ (desc A) → Tree A
from A leaf-β = leaf-α
from A (node1-β v xs) = node1-α v (from A xs)
from A (node2-β v xs ys) = node2-α v (from A xs) (from A ys)
from A absurd-β

to-from : (A : Set) → ∀ x → from A (to A x) ≡ x
to-from A leaf-α = refl
to-from A (node1-α v xs) = cong (node1-α v) (to-from A xs)
to-from A (node2-α v xs ys) = cong₂ (node2-α v) (to-from A xs) (to-from A ys)

from-to : (A : Set) → ∀ x → to A (from A x) ≡ x
from-to A leaf-β = refl
from-to A (node1-β v xs) = cong (node1-β v) (from-to A xs)
from-to A (node2-β v xs ys) = cong₂ (node2-β v) (from-to A xs) (from-to A ys)
from-to A absurd-β

qdt : NamedSafeDatatype
qdt = quoteDatatypeᵐ Tree

module TestQdt where
  open import Builtin.Reflection
  open import ContextFree.One.Params
  test-qdt : qdt ≡ mk (quote Tree) 1 (param₀ visible "A" ∷ [])
                      ((quote leaf , []) ∷
                       (quote node1 , Spar 0 ∷ Srec ∷ []) ∷
                       (quote node2 , Spar 0 ∷ Srec ∷ Srec ∷ []) ∷
                       [])
  test-qdt = refl

unquoteDecl qrec = defineRecord qrec qdt

module Q (A : Set) = RawIsContextFree (qrec A)

testDesc : ∀{A} → Q.desc A ≡ desc A
testDesc = refl

testTo : ∀{A} t → Q.to A t ≡ to A t
testTo leaf-α = refl
testTo (node1-α v xs) = cong (node1-β v) (testTo xs)
testTo (node2-α v xs ys) = cong₂ (node2-β v) (testTo xs) (testTo ys)
