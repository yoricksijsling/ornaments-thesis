
module Cx.Simple.Examples where

open import Common
open import Cx.Simple.Ornament

natD : DatDesc 2
natD = ι ⊕ (rec-⊗ ι) ⊕ `0
natD-zero : μ natD
natD-zero = ⟨ 0 , tt ⟩
natD-suc : μ natD → μ natD
natD-suc n = ⟨ 1 , n , tt ⟩


listD : (A : Set) → DatDesc 2
listD A = ι ⊕ ((λ γ → A) ⊗ rec-⊗ ι) ⊕ `0
listD-nil : ∀{A} → μ (listD A)
listD-nil = ⟨ 0 , tt ⟩
listD-cons : ∀{A} → A → μ (listD A) → μ (listD A)
listD-cons x xs = ⟨ 1 , x , xs , tt ⟩


module NatToList where
  nat→slist : DatOrn natD
  -- nat→list A = ? ⊕ ? ⊕ `0
  nat→slist = ι ⊕ (insert (λ δ → String) ⊗ rec-⊗ ι) ⊕ `0

  test-nat→slist : ornToDesc nat→slist ≡ listD String
  test-nat→slist = refl

  ex-list : μ (listD String)
  ex-list = listD-cons "Test" (listD-cons "one" (listD-cons "two" listD-nil))
  -- ex-list = ⟨ 1 , "Test" , ⟨ 1 , "one" , ⟨ 1 , "two" , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩ , tt ⟩

  forget-list : forget nat→slist ex-list ≡ natD-suc (natD-suc (natD-suc natD-zero))
  -- forget-list : forget nat→slist ex-list ≡ ⟨ 1 , ⟨ 1 , ⟨ 1 , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩ , tt ⟩
  forget-list = refl

