
module Cx.Named.Examples where

open import Common
open import Cx.Named.Ornament String {{ShowString}}
-- open import Cx.Named.Desc String {{ShowString}}

natD : DatDesc ⊤ ε 2
natD = "zero" ∣ ι (λ _ → tt)
     ⊕ "suc" ∣ "n" /rec (λ _ → tt) ⊗ ι (λ _ → tt)
     ⊕ `0

-- natD : DatDesc ⊤ ε 2
-- natD = ι (λ _ → tt)
--        ⊕ rec (λ _ → tt) ⊗ ι (λ _ → tt)
--        ⊕ `0
-- natD-zero : μ natD tt tt
-- natD-zero = ⟨ 0 , refl ⟩
-- natD-suc : μ natD tt tt → μ natD tt tt
-- natD-suc n = ⟨ 1 , n , refl ⟩

-- data List (A : Set) : Set where
--   [] : List A
--   _∷_ : A → List A → List A
  
listD : DatDesc ⊤ (ε ▷Set) 2
listD = "lo" ∣ ι (λ _ → tt)
      ⊕ "la" ∣ "_" / top ⊗ "_" /rec (λ _ → tt) ⊗ ι (λ _ → tt)
      ⊕ `0

-- listD : DatDesc ⊤ (ε ▷Set) 2
-- listD = ι (λ _ → tt)
--       ⊕ top ⊗ rec (λ _ → tt) ⊗ ι (λ _ → tt)
--       ⊕ `0
-- listD-nil : ∀{A} → μ listD (tt , A) tt
-- listD-nil = ⟨ 0 , refl ⟩
-- listD-cons : ∀{A} → A → μ listD (tt , A) tt → μ listD (tt , A) tt
-- listD-cons x xs = ⟨ 1 , x , xs , refl ⟩

-- vecD : DatDesc Nat (ε ▷Set) 2
-- vecD = ι (λ _ → 0)
--      ⊕ (λ _ → Nat) ⊗ (top ∘ pop) ⊗ rec (top ∘ pop) ⊗ ι (suc ∘ top ∘ pop)
--      ⊕ `0
