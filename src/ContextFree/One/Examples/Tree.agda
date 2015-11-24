module ContextFree.One.Examples.Tree where

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

data Tree (A : Set) : Set where
  leaf : Tree A
  node1 : A → Tree A → Tree A
  node2 : A → Tree A → Tree A → Tree A

desc : (A : Set) → Desc
desc A = `1 `+ (`P₀ A `* `rec `* `1) `+ (`P₀ A `* `rec `* `rec `* `1) `+ `0

pattern leaf-α = leaf
pattern leaf-β = ⟨ inj₁ tt ⟩
pattern node1-α v xs = node1 v xs
pattern node1-β v xs = ⟨ inj₂ (inj₁ (v , xs , tt)) ⟩
pattern node2-α v xs ys = node2 v xs ys
pattern node2-β v xs ys = ⟨ inj₂ (inj₂ (inj₁ (v , xs , ys , tt))) ⟩
pattern absurd-β = ⟨ inj₂ (inj₂ (inj₂ ())) ⟩

to : (A : Set) → Tree A → μ (desc A)
to A leaf-α = leaf-β
to A (node1-α v xs) = node1-β v (to A xs)
to A (node2-α v xs ys) = node2-β v (to A xs) (to A ys)

from : (A : Set) → μ (desc A) → Tree A
from A leaf-β = leaf-α
from A (node1-β v xs) = node1-α v (from A xs)
from A (node2-β v xs ys) = node2-α v (from A xs) (from A ys)
from A absurd-β

qdt : NamedSafeDatatype
qdt = quoteDatatype! (quote Tree) 1

qdesc : DescFun (proj₁ (unnameSafeDatatype qdt))
qdesc = descFun (proj₁ (unnameSafeDatatype qdt))
unquoteDecl qto = makeTo qto (quote qdesc) qdt
unquoteDecl qfrom = makeFrom qfrom (quote qdesc) qdt
unquoteDecl qcf = makeRecord (quote qdesc) (quote qto) (quote qfrom) qdt

testDesc : ∀{A} → qdesc A ≡ desc A
testDesc = refl

testTo : ∀{A} t → qto A t ≡ to A t
testTo leaf = refl
testTo (node1 v xs) = cong (λ xs′ → ⟨ inj₂ (inj₁ (v , xs′ , tt)) ⟩) (testTo xs)
testTo (node2 v xs ys) = cong₂ (λ xs′ ys′ → ⟨ inj₂ (inj₂ (inj₁ (v , xs′ , ys′ , tt))) ⟩) (testTo xs) (testTo ys)
