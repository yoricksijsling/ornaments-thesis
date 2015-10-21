module SPT.Examples.Maybe where

open import Data.Fin using (#_; zero; suc)
open import Data.Maybe.Base
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Unit.Base
open import Function
open import Relation.Binary.PropositionalEquality

open import SPT.Desc

instance
  isSPT-Maybe : ∀ A → IsSPT (Maybe A)
  isSPT-Maybe A = record
    { desc = `σ 2 λ { zero → `K A
                    ; (suc zero) → `1
                    ; (suc (suc ()))
                    }
    ; to = λ { (just x) → ⟨ # 0 , x ⟩ ; nothing → ⟨ # 1 , tt ⟩ }
    ; from = λ { ⟨ zero , x ⟩ → just x
               ; ⟨ suc zero , tt ⟩ → nothing
               ; ⟨ suc (suc ()) , _ ⟩
               }
    }

import SPT.Folding
open module F {A : Set} = SPT.Folding {{isSPT-Maybe A}}

testFold : Maybe ℕ → ℕ
testFold = fold λ { (zero , x) → x
                  ; (suc zero , tt) → 0
                  ; (suc (suc ()) , _)
                  }

test1 : testFold (just 5) ≡ 5
test1 = refl

test2 : testFold nothing ≡ 0
test2 = refl
