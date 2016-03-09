module ContextFree.Multi.Examples.Fin where

open import Common
open import ContextFree.Multi.Desc
open import ContextFree.Multi.Quotable
open import ContextFree.Multi.Quoted
open import ContextFree.Multi.Quoting

-- data Fin : Nat → Set where
--   zero : ∀ {n} → Fin (suc n)
--   suc  : ∀ {n} (i : Fin n) → Fin (suc n)

pattern zero-α n = zero {n}
pattern zero-β n = ⟨ left (n , refl , tt) ⟩
pattern suc-α n i = suc {n} i
pattern suc-β n i = ⟨ right (left (n , i , refl , tt)) ⟩
pattern absurd-β = ⟨ right (right ()) ⟩

module Manually where
  desc : IODesc (Fin 0) Nat
  desc = `fix $ `ΣK Nat (λ n → `! (suc n) `* `1) `+
                `ΣK Nat (λ n → `var (right n) `* `! (suc n) `* `1) `+
                `0

  req : ISet (Fin 0)
  req ()

  -- The (suc n) pattern comes directly from the requirement `! (suc n).
  -- In the product, (`ΣK _ λ x → ..) translates to (x) and (`! o′) translates
  -- to (refl).
  -- In this particular case we do not have to pattern match on n, but we do it
  -- to have n available as a variable on the right hand side.
  to : ∀ n → Fin n → ⟦ desc ⟧ req n
  -- to (suc n) zero = ⟨ left (n , refl , tt) ⟩
  -- to (suc n) (suc i) = ⟨ right (left (n , to n i , refl , tt)) ⟩
  to ._ (zero-α n) = zero-β n
  to ._ (suc-α n i) = suc-β n (to n i)

  from : ∀ n → ⟦ desc ⟧ req n → Fin n
  -- from ._ ⟨ left (n , refl , tt) ⟩ = zero
  -- from ._ ⟨ right (left (n , i , refl , tt)) ⟩ = suc (from _ i)
  -- from _ ⟨ right (right ()) ⟩
  from ._ (zero-β n) = zero-α n
  from ._ (suc-β n i) = suc-α n (from n i) -- n comes from (`var (right n))
  from _ absurd-β

  to-from : ∀ n i → from n (to n i) ≡ i
  to-from ._ (zero-α n) = refl
  to-from ._ (suc-α n i) = cong (suc-α n) (to-from _ i)

  from-to : ∀ n i → to n (from n i) ≡ i
  from-to ._ (zero-β n) = refl
  from-to ._ (suc-β n i) = cong (suc-β n) (from-to n i)
  from-to _ absurd-β

  rec : ∀ n → Quotable (Fin n)
  rec n = record { desc = desc ; to = to n ; from = from n
                 ; to-from = to-from n ; from-to = from-to n }

-- nsdt : NamedSafeDatatype
-- nsdt = quoteDatatypeᵐ Nat

-- module TestNsdt where
--   open import Builtin.Reflection
--   open import ContextFree.Multi.Params
--   test-nsdt : nsdt ≡ mk (quote Nat) 0 []
--                       ((quote Nat.zero , []) ∷
--                        (quote Nat.suc , Srec ∷ []) ∷
--                        [])
--   test-nsdt = refl

-- unquoteDecl qrec = defineRecord qrec nsdt

-- module TestQrec where
--   module Q = RawIsContextFree qrec
--   module M = IsContextFree Manually.rec

--   test-desc : Q.desc ≡ M.desc
--   test-desc = refl

--   test-req : ∀ x → Q.req x ≡ M.req x
--   test-req ()

--   test-to : {{rs : Q.req ≡ M.req}} → ∀ x → DescEq (`fix Q.desc) (Q.to x) (M.to x)
--   test-to zero = ⟨⟩-cong (left-cong tt-cong)
--   test-to (suc n) = ⟨⟩-cong (right-cong (left-cong (,-cong (var-cong (DescEq-to-≅ (test-to n))) tt-cong)))

--   test-from : {{rs : Q.req ≡ M.req}} → ∀ {x y} → DescEq (`fix Q.desc) x y → Q.from x ≅ Q.from y
--   test-from (⟨⟩-cong (left-cong tt-cong)) = refl
--   test-from (⟨⟩-cong (right-cong (left-cong (,-cong (var-cong refl) tt-cong)))) = refl
--   test-from (⟨⟩-cong (right-cong (right-cong ())))
