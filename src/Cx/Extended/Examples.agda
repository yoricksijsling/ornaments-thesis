
module Cx.Extended.Examples where

open import Common
open import Cx.Extended.Ornament

natD : DatDesc ⊤ ε 2
natD = ι (λ _ → tt)
       ⊕ rec (λ _ → tt) ⊗ ι (λ _ → tt)
       ⊕ `0
natD-zero : μ natD tt tt
natD-zero = ⟨ 0 , refl ⟩
natD-suc : μ natD tt tt → μ natD tt tt
natD-suc n = ⟨ 1 , n , refl ⟩

listD : DatDesc ⊤ (ε ▷Set) 2
listD = ι (λ _ → tt)
      ⊕ top ⊗ rec (λ _ → tt) ⊗ ι (λ _ → tt)
      ⊕ `0
listD-nil : ∀{A} → μ listD (tt , A) tt
listD-nil = ⟨ 0 , refl ⟩
listD-cons : ∀{A} → A → μ listD (tt , A) tt → μ listD (tt , A) tt
listD-cons x xs = ⟨ 1 , x , xs , refl ⟩

vecD : DatDesc Nat (ε ▷Set) 2
vecD = ι (λ _ → 0)
     ⊕ (λ _ → Nat) ⊗ (top ∘ pop) ⊗ rec (top ∘ pop) ⊗ ι (suc ∘ top ∘ pop)
     ⊕ `0


module NatToList where
  -- Index stays ⊤. Parameters become (ε ▷Set).
  nat→list : DefOrn ⊤ id (ε ▷Set) (mk (λ _ → tt)) natD
  nat→list = ι (λ δ → inv tt)
           ⊕ insert top ⊗ rec (λ δ → inv tt) ⊗ ι (λ δ → inv tt)
           ⊕ `0
  test-nat→list : ornToDesc nat→list ≡ listD
  test-nat→list = refl


module ListToNatList where
  list-ex : μ listD (tt , Nat) tt
  list-ex = ⟨ 1 , 100 , ⟨ 1 , 33 , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩

  list→natlist : DefOrn ⊤ id ε (mk (_, Nat)) listD
  list→natlist = ι (λ _ → inv tt)
               ⊕ -⊗ rec (λ _ → inv tt) ⊗ ι (λ _ → inv tt)
               ⊕ `0

  natlist-ex : μ (ornToDesc list→natlist) tt tt
  natlist-ex = ⟨ 1 , 100 , ⟨ 1 , 33 , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩


module ListToVec where
  list→vec : DefOrn Nat (λ _ → tt) (ε ▷Set) (cxf-id _) listD
  list→vec = ι (λ _ → inv 0)
           ⊕ insert (λ _ → Nat) ⊗ -⊗ rec (inv ∘ top ∘ pop) ⊗ ι (inv ∘ suc ∘ top ∘ pop)
           ⊕ `0
  test-list→vec : ornToDesc list→vec ≡ vecD
  test-list→vec = refl


open import Cx.Extended.AlgebraicOrnament

module LengthAlgebra where
  lengthAlg : ∀ {A} → Alg listD (tt , A) (λ tt → Nat)
  lengthAlg (zero , refl) = 0
  lengthAlg (suc zero , x , xs , refl) = suc xs
  lengthAlg (suc (suc ()) , _)

  list→vec : DefOrn (⊤ × Nat) fst (ε ▷Set) (cxf-id _) listD
  list→vec = algOrn listD lengthAlg

  vecD′ : DatDesc (⊤ × Nat) (ε ▷Set) 2
  vecD′ = ι (λ _ → (tt , 0))
        ⊕ top ⊗ (λ _ → Nat) ⊗ rec (λ γ → tt , top γ) ⊗ ι (λ γ → tt , suc (top γ))
        ⊕ `0

  test-list→vec : ornToDesc list→vec ≡ vecD′
  test-list→vec = refl

module ReornamentNatToList where
  open NatToList

  nat→vec : DefOrn (⊤ × μ natD tt tt) fst (ε ▷Set) (mk (λ _ → tt)) natD
  nat→vec = reornament nat→list

  vecD′ : DatDesc (⊤ × μ natD tt tt) (ε ▷Set) 2
  vecD′ = ι (λ _ → (tt , natD-zero))
        ⊕ top ⊗ (λ _ → μ natD tt tt) ⊗ rec (λ γ → tt , top γ) ⊗ ι (λ γ → tt , natD-suc (top γ))
        ⊕ `0

  test-nat→vec : ornToDesc nat→vec ≡ vecD′
  test-nat→vec = refl

  ex-vec : μ (ornToDesc nat→vec) (tt , Nat) (tt , (natD-suc (natD-suc natD-zero)))
  ex-vec = ⟨ 1 , 33 , _ , ⟨ 1 , 44 , _ , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩

  test-forget-vec : forget nat→vec ex-vec ≡ natD-suc (natD-suc natD-zero)
  test-forget-vec = refl
