module SPT1.Examples.Nat where

open import Data.Fin
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Function

open import SPT1.Desc

data Nat : Set where
  ze : Nat
  su : Nat → Nat

isSPT-ℕ : IsSPT ℕ
isSPT-ℕ = record { desc = desc ; to = to ; from = from }
  where
  desc : Desc
  desc = `Σ (Fin 2) λ { zero → `1
                      ; (suc zero) → `Σ (⟦ `var ⟧ {!!}) {!!}
                      ; (suc (suc ()))
                      }
  to : ℕ → μ desc
  to = {!!}
  from : μ desc → ℕ
  from = {!!}
