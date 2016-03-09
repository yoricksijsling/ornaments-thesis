module ContextFree.Multi.Examples.Unit where

open import Common
open import ContextFree.Multi.Desc
open import ContextFree.Multi.Quotable
open import ContextFree.Multi.Quoted
open import ContextFree.Multi.Quoting

data U : Set where
  u : U

desc : IODesc (Fin 0) ⊤
desc = `fix $ `1 `+ `0

pattern α = u
pattern β = ⟨ left tt ⟩
pattern absurd-β = ⟨ right () ⟩

req : ISet (Fin 0)
req ()

to : U → ⟦ desc ⟧ req tt
to α = β

from : ⟦ desc ⟧ req tt → U
from β = α
from absurd-β

to-from : ∀ x → from (to x) ≡ x
to-from α = refl

from-to : ∀ x → to (from x) ≡ x
from-to β = refl
from-to absurd-β

isContextFree-U : Quotable U
isContextFree-U = record { desc = desc ; to = to ; from = from
                         ; to-from = to-from ; from-to = from-to }

nsdt : NamedSafeDatatype
nsdt = quoteDatatypeᵐ U

module TestNsdt where
  open import Builtin.Reflection
  open import ContextFree.Multi.Params
  test-nsdt : nsdt ≡ mk (quote U) [] [] ((quote u , []) ∷ [])
  test-nsdt = refl

unquoteDecl qrec = defineRecord qrec nsdt

module Q = RawQuotable qrec

testDesc : Q.desc ≡ desc
testDesc = refl

test-req : ∀ x → Q.req x ≡ req x
test-req ()

test-to : {{rs : Q.req ≡ req}} → ∀ x → DescEq Q.desc (Q.to x) (to x)
test-to u = ⟨⟩-cong $ left-cong tt-cong

test-from : ∀ {x y} → DescEq Q.desc x y → Q.from x ≡ from y
test-from (⟨⟩-cong (left-cong tt-cong)) = refl
test-from (⟨⟩-cong (right-cong ()))

module WithExtensionality where
  postulate
    ext : ∀ {a b} → Extensionality a b

  test-to′ : ∀ x → Q.to x ≅ to x
  test-to′ = DescEq-to-≅ {{ext (test-req)}} ∘ test-to {{ext (test-req)}}

  test-from′ : ∀ {x y} → x ≅ y → Q.from x ≡ from y
  test-from′ = test-from ∘ DescEq-from-≅ {{ext test-req}}
