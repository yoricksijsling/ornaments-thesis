module ContextFree.Multi.Examples.Vec where

open import Common
open import ContextFree.Multi.Desc
open import ContextFree.Multi.Quotable
open import ContextFree.Multi.Quoted
open import ContextFree.Multi.Quoting

data VecP (A : Set) : Nat → Set where
  nil  : VecP A zero
  cons : ∀ n (x : A) (xs : VecP A n) → VecP A (suc n)

pattern nil-α = nil
pattern nil-β = ⟨ left (refl , tt) ⟩
pattern cons-α n x xs = cons n x xs
pattern cons-β n x xs = ⟨ right (left (n , x , xs , refl , tt)) ⟩
pattern absurd-β = ⟨ right (right ()) ⟩

module Manually where
  desc : IODesc (Fin 1) Nat
  desc = `fix $ `! zero `* `1 `+
                `ΣK Nat (λ n → `var (left 0) `* `var (right n) `* `! (suc n) `* `1) `+
                `0

  req : (A : Set) → ISet (Fin 1)
  req A zero = A
  req A (suc ())

  to : ∀ A n → VecP A n → ⟦ desc ⟧ (req A) n
  to A ._ nil-α = nil-β
  to A ._ (cons-α n x xs) = cons-β n x (to A n xs)

  from : ∀ A n → ⟦ desc ⟧ (req A) n → VecP A n
  from A ._ nil-β = nil-α
  from A ._ (cons-β n x xs) = cons-α n x (from A n xs)
  from A _ absurd-β

  to-from : ∀ A n x → from A n (to A n x) ≡ x
  to-from A ._ nil-α = refl
  to-from A ._ (cons-α n x xs) = cong (cons-α n x) (to-from A n xs)

  from-to : ∀ A n x → to A n (from A n x) ≡ x
  from-to A ._ nil-β = refl
  from-to A ._ (cons-β n x xs) = cong (cons-β n x) (from-to A n xs)
  from-to A _ absurd-β

-- nsdt : NamedSafeDatatype
-- nsdt = quoteDatatypeᵐ VecP

-- data VecP (A : Set) : Nat → Set where
--   nil  : VecP A zero
--   cons : ∀ n (x : A) (xs : VecP A n) → VecP A (suc n)

-- module TestQdt where
--   open import Builtin.Reflection
--   open import ContextFree.Multi.Params

--   test-nsdt : nsdt ≡ mk (quote VecP) 1 (param₀ visible "A" ∷ [])
--                         ((quote VecP.[]  , []) ∷
--                          (quote VecP._∷_ , Spar 0 ∷ Srec ∷ []) ∷
--                          [])
--   test-nsdt = refl

  -- sdt ≡ mk
  --       1 (param₀ visible "A" ∷ [])
  --       1 (paramx visible "_" Nat ∷ [])
  --       ([] , con₀ zero)
  --       (Sk Nat ∷ Spar 0 ∷ Srec (var₀ 1) ∷ [] , con₁ suc (var₀ 2))
