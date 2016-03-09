module ContextFree.Multi.Examples.Pair where

open import Common
open import ContextFree.Multi.Desc
open import ContextFree.Multi.Quotable
open import ContextFree.Multi.Quoted
open import ContextFree.Multi.Quoting

data Pair (A B : Set) : Set where
  pair : (a : A) → (b : B) → Pair A B

module Manually where
  desc : IODesc (Fin 2) ⊤
  desc = `fix $ `var (left 0) `* `var (left 1) `* `1 `+ `0

  pattern α a b = pair a b
  pattern β a b = ⟨ left (a , b , tt) ⟩
  pattern absurd-β = ⟨ right () ⟩

  req : (A B : Set) → ISet (Fin 2)
  req A B zero = A
  req A B (suc zero) = B
  req A B (suc (suc ()))

  to : (A B : Set) → Pair A B → ⟦ desc ⟧ (req A B) tt
  to A B (α a b) = β a b

  from : (A B : Set) → ⟦ desc ⟧ (req A B) tt → Pair A B
  from A B (β a b) = α a b
  from A B absurd-β

  to-from : (A B : Set) → ∀ x → from A B (to A B x) ≡ x
  to-from A B (α a b) = refl

  from-to : (A B : Set) → ∀ x → to A B (from A B x) ≡ x
  from-to A B (β a b) = refl
  from-to A B absurd-β

  rec : ∀ A B → Quotable (Pair A B)
  rec A B = record { desc = desc ; to = to A B ; from = from A B
                   ; to-from = to-from A B ; from-to = from-to A B }

nsdt : NamedSafeDatatype
nsdt = quoteDatatypeᵐ Pair

module TestNsdt where
  open import Builtin.Reflection
  open import ContextFree.Multi.Params
  test-nsdt : nsdt ≡ mk (quote Pair) (param₀ visible "A" ∷ param₀ visible "B" ∷ []) []
                      ((quote pair , Spar 1 ∷ Spar 0 ∷ []) ∷
                       [])
  test-nsdt = refl

unquoteDecl qrec = defineRecord qrec nsdt

module TestQrec (A B : Set) where
  module Q = RawQuotable (qrec A B)
  module M = Quotable (Manually.rec A B)

  test-desc : Q.desc ≡ M.desc
  test-desc = refl

  test-req : (i : Fin 2) → Q.req i ≡ M.req i
  test-req zero = refl
  test-req (suc zero) = refl
  test-req (suc (suc ()))

  test-to : {{rs : Q.req ≡ M.req}} → ∀ x → DescEq Q.desc (Q.to x) (M.to x)
  test-to (pair a b) = ⟨⟩-cong (left-cong (,-cong (var-cong refl) (,-cong (var-cong refl) tt-cong)))

  test-from : {{rs : Q.req ≡ M.req}} → ∀ {x y} → DescEq Q.desc x y → Q.from x ≅ M.from y
  test-from (⟨⟩-cong (left-cong (,-cong (var-cong refl) (,-cong (var-cong refl) tt-cong)))) = refl
  test-from (⟨⟩-cong (right-cong ()))
