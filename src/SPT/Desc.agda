{-# OPTIONS --type-in-type #-}

module SPT.Desc where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Unit

-- SPT : 0, 1, ×, +, μ, def, wk, vl, →, fun

open import Function

mutual
  data Desc : Set₁ where
    `1 : Desc
    `K : (S : Set) → Desc
    `Σ : (S : Desc) → (D : μ S → Desc) → Desc -- We need dependent product. Sadly, the Desc is a Set₁ so we need type-in-type. We can not stratify it because the level can't be used as an index.
    `var : Desc
    -- _`→_ : (H : Desc) → (D : μ H → Desc) → Desc
    `σ : (n : ℕ)(D : Fin n → Desc) → Desc -- + and 0, could also be done with Σ
    _`×_ : (A B : Desc) → Desc -- First-order product
  
  ⟦_⟧ : Desc → Set → Set
  ⟦_⟧ `1 X = ⊤
  ⟦_⟧ (`K S) X = S
  ⟦_⟧ (`Σ S D) X = Σ (μ S) λ s → ⟦ D s ⟧ X
  ⟦_⟧ `var X = X
  -- ⟦_⟧ (H `→ D) X = (h : μ H) → ⟦ D h ⟧ X
  ⟦_⟧ (`σ n D) X = Σ (Fin n) λ k → ⟦ D k ⟧ X
  ⟦_⟧ (A `× B) X = ⟦ A ⟧ X × ⟦ B ⟧ X
  
  data μ (D : Desc) : Set where
    ⟨_⟩ : ⟦ D ⟧ (μ D) → μ D

  out : ∀{D} → μ D → ⟦ D ⟧ (μ D)
  out ⟨ x ⟩ = x

record IsSPT (A : Set) : Set₁ where
  field
    desc : Desc
    to : A → μ desc
    from : μ desc → A
    -- should be inverses

