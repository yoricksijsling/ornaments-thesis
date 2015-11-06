module ContextFree.One.Examples.Pair where

open import ContextFree.One.Desc
open import ContextFree.One.Quoting
open import ContextFree.One.Quoted
open import ContextFree.One.Unquoting (quote Desc) (quote μ)
open import Data.Unit.Base
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

data Pair (A B : Set) : Set where
  pair : (a : A) → (b : B) → Pair A B

isContextFree-Pair : ∀ A B → IsContextFree (Pair A B)
isContextFree-Pair A B = record { desc = desc ; to = to ; from = from
                                ; to-from = to-from ; from-to = from-to }
  where
  desc : Desc
  desc = `K A `* `K B `* `1 `+ `0
  to : Pair A B → μ desc
  to (pair a b) = ⟨ inj₁ (a , b , tt) ⟩
  from : μ desc → Pair A B
  from ⟨ inj₁ (a , b , tt) ⟩ = pair a b
  from ⟨ inj₂ () ⟩
  to-from : ∀ x → from (to x) ≡ x
  to-from (pair a b) = refl
  from-to : ∀ x → to (from x) ≡ x
  from-to ⟨ inj₁ (a , b , tt) ⟩ = refl
  from-to ⟨ inj₂ () ⟩

open module Foo (A B : Set) = IsContextFree (isContextFree-Pair A B)

qdt : SafeDatatype
qdt = quoteDatatype! (quote Pair) 2

unquoteDecl qdesc = makeDesc qdt
unquoteDecl qto = makeTo (quote qdesc) qto qdt

testDesc : ∀{A B} → qdesc A B ≡ desc A B
testDesc = refl

testTo : ∀{A B} x → qto A B x ≡ to A B x
testTo (pair a b) = refl

