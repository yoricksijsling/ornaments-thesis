
module Thesis.Extended where

open import Common
open import Cx.Extended hiding (⟦_⟧desc; fold)

{-# TERMINATING #-}
⟦_⟧desc : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → Pow ⟦ I ⟧ → Pow ⟦ I ⟧
⟦_⟧desc {dt = isCon} (ι o) γ X o′ = o γ ≡ o′
⟦_⟧desc {dt = isCon} (S ⊗ xs) γ X o = Σ (S γ) λ s → ⟦ xs ⟧desc (γ , s) X o
⟦_⟧desc {dt = isCon} (rec i ⊗ xs) γ X o = X (i γ) × ⟦ xs ⟧desc γ X o
⟦_⟧desc {dt = isDat #c} D γ X o = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧desc γ X o

{-# TERMINATING #-}
fold : ∀{I Γ #c}{D : DatDesc I Γ #c}{γ X} (α : Alg D γ X) →
       {i : ⟦ I ⟧} → μ D γ i → X i
fold {D = D} α ⟨ xs ⟩ = α (descmap (fold α) D xs)
