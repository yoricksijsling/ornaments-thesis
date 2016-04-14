
module Cx.Named.Examples where

open import Common
open import Cx.Named.Ornament

natD : DatDesc ⊤ ε 2
natD = "zero" ∣ ι (λ _ → tt)
     ⊕ "suc" ∣ "n" /rec (λ _ → tt) ⊗ ι (λ _ → tt)
     ⊕ `0
natD-zero : μ natD tt tt
natD-zero = ⟨ 0 , refl ⟩
natD-suc : μ natD tt tt → μ natD tt tt
natD-suc n = ⟨ 1 , n , refl ⟩
  
listD : DatDesc ⊤ (ε ▷₁ (λ _ → Set)) 2
listD = "nil" ∣ ι (λ _ → tt)
      ⊕ "cons" ∣ "_" / top ⊗ "_" /rec (λ _ → tt) ⊗ ι (λ _ → tt)
      ⊕ `0
listD-nil : ∀{A} → μ listD (tt , A) tt
listD-nil = ⟨ 0 , refl ⟩
listD-cons : ∀{A} → A → μ listD (tt , A) tt → μ listD (tt , A) tt
listD-cons x xs = ⟨ 1 , x , xs , refl ⟩

-- vecD : DatDesc Nat (ε ▷Set) 2
-- vecD = ι (λ _ → 0)
--      ⊕ (λ _ → Nat) ⊗ (top ∘ pop) ⊗ rec (top ∘ pop) ⊗ ι (suc ∘ top ∘ pop)
--      ⊕ `0

module NatToList where
  -- Index stays ⊤. Parameters become (ε ▷Set).
  nat→list : DefOrn ⊤ id (ε ▷₁ (λ γ → Set)) (mk (λ _ → tt)) natD
  nat→list = {!!} ∣ {!!}
           ⊕ {!!} ∣ {!!}
           ⊕ {!!}
  -- ι (λ δ → inv tt)
  --          ⊕ insert top ⊗ rec (λ δ → inv tt) ⊗ ι (λ δ → inv tt)
  --          ⊕ `0
  test-nat→list : ornToDesc nat→list ≡ listD
  test-nat→list = refl
