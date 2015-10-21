-- FROM: the essence of ornaments

module Signature where

open import Data.Product

-- Many-sorted signatures are also implemented in the Glorious
-- Standard library under the heading of
-- 'Data.Container.Indexed'. This file gives a simplified version of
-- those definitions.

record Sig (I : Set) : Set₁ where
  constructor _◃_/_
  field
    Op : (i : I) → Set
    Ar : ∀ {i} → Op i → Set
    Ty : ∀ {i}{op : Op i} → Ar op → I


⟦_⟧ : ∀{I} → Sig I → (I → Set) → I → Set
⟦ Op ◃ Ar / Ty ⟧ X i = Σ[ op ∈ Op i ] ((ar : Ar op) → X (Ty ar))


data μ {I}(Σ : Sig I)(i : I) : Set where
  ⟨_⟩ : ⟦ Σ ⟧ (μ Σ) i → μ Σ i


_∘_ : ∀{I} → Sig I → Sig I → Sig I
Σ₂ ∘ Σ₁ = (λ i → Σ[ op₁ ∈ Op Σ₁ i ] ((ar₁ : Ar Σ₁ op₁) → Op Σ₂ (Ty Σ₁ ar₁))) 
        ◃ (λ { (op₁ , ops₂) → Σ[ ar₁ ∈ Ar Σ₁ op₁ ] Ar Σ₂ (ops₂ ar₁) }) 
        / (λ { (ar₁ , ar₂) → Ty Σ₂ ar₂ })
  where open Sig
