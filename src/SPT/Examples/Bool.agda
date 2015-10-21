module SPT.Examples.Bool where

open import Data.Bool
open import Data.Fin using (#_; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Unit
open import Function
open import SPT.Desc
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

instance
  isSPT-Bool : IsSPT Bool
  isSPT-Bool = record
    { desc = `σ 2 (const `1)
    ; to = λ x → if x then ⟨ # 0 , tt ⟩ else ⟨ # 1 , tt ⟩
    ; from = λ { ⟨ zero , tt ⟩ → true
               ; ⟨ suc zero , tt ⟩ → false
               ; ⟨ suc (suc ()) , _ ⟩ }
    }

open import SPT.Folding

testFold : Bool → ℕ
testFold = fold (λ { (zero , tt) → 10
                   ; (suc zero , tt) → 20
                   ; (suc (suc ()) , tt)
                   })

test1 : testFold true ≡ 10
test1 = refl

test2 : testFold false ≡ 20
test2 = refl
