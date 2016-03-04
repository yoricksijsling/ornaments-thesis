module ContextFree.Multi.Examples.Nat where

open import Common
open import ContextFree.Multi.Desc
open import ContextFree.Multi.DescEquality
open import ContextFree.Multi.DescFunction
open import ContextFree.Multi.EmbeddingProjection
open import ContextFree.Multi.Quoted
open import ContextFree.Multi.Quoting

pattern zero-α = zero
pattern zero-β = ⟨ left tt ⟩
pattern suc-α n = suc n
pattern suc-β n = ⟨ right (left (n , tt)) ⟩
pattern absurd-β = ⟨ right (right ()) ⟩

module Manually where
  desc : IODesc (Either (Fin 0) ⊤) ⊤
  desc = `1 `+ (`var (right tt) `* `1) `+ `0

  req : Fin 0 → Set
  req ()

  to : Nat → ⟦ `fix desc ⟧ req tt
  to zero-α = zero-β
  to (suc-α n) = suc-β (to n)

  from : ⟦ `fix desc ⟧ req tt → Nat
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

  rec : IsContextFree Nat
  rec = record { desc = desc ; to = to ; from = from
               ; to-from = to-from ; from-to = from-to }

nsdt : NamedSafeDatatype
nsdt = quoteDatatypeᵐ Nat

module TestNsdt where
  open import Builtin.Reflection
  open import ContextFree.Multi.Params
  test-nsdt : nsdt ≡ mk (quote Nat) 0 []
                      ((quote Nat.zero , []) ∷
                       (quote Nat.suc , Srec ∷ []) ∷
                       [])
  test-nsdt = refl

unquoteDecl qrec = defineRecord qrec nsdt

module TestQrec where
  module Q = RawIsContextFree qrec
  module M = IsContextFree Manually.rec

  test-desc : Q.desc ≡ M.desc
  test-desc = refl

  test-req : ∀ x → Q.req x ≡ M.req x
  test-req ()

  test-to : {{rs : Q.req ≡ M.req}} → ∀ x → DescEq (`fix Q.desc) (Q.to x) (M.to x)
  test-to zero = ⟨⟩-cong (left-cong tt-cong)
  test-to (suc n) = ⟨⟩-cong (right-cong (left-cong (,-cong (var-cong (DescEq-to-≅ (test-to n))) tt-cong)))

  test-from : {{rs : Q.req ≡ M.req}} → ∀ {x y} → DescEq (`fix Q.desc) x y → Q.from x ≅ Q.from y
  test-from (⟨⟩-cong (left-cong tt-cong)) = refl
  test-from (⟨⟩-cong (right-cong (left-cong (,-cong (var-cong refl) tt-cong)))) = refl
  test-from (⟨⟩-cong (right-cong (right-cong ())))
