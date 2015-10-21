module SPT.Examples.Nat where

open import Data.Fin using (Fin; #_; zero; suc)
open import Data.Maybe.Base
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
open import Data.Unit.Base
open import Function
open import Relation.Binary.PropositionalEquality

open import SPT.Desc

instance
  isSPT-ℕ : IsSPT ℕ
  isSPT-ℕ = record { desc = desc ; to = to ; from = from }
    where
    desc : Desc
    desc = `σ 2 λ { zero → `1
                  ; (suc zero) → `var
                  ; (suc (suc ()))
                  }
    to : ℕ → μ desc
    to zero = ⟨ # 0 , tt ⟩
    to (suc n) = ⟨ # 1 , to n ⟩
    from : μ desc → ℕ
    from ⟨ zero , tt ⟩ = 0
    from ⟨ suc zero , n ⟩ = suc (from n)
    from ⟨ suc (suc ()) , _ ⟩
