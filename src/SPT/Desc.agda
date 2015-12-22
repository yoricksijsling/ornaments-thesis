{-# OPTIONS --type-in-type #-}

module SPT.Desc where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Unit


module Min where
  data Desc : Set where
    `1 : Desc
    `Σ : (S : Set) → (D : S → Desc) → Desc
    `var : Desc

  ⟦_⟧ : Desc → Set → Set
  ⟦_⟧ `1 X = ⊤
  ⟦_⟧ (`Σ S D) X = Σ[ s ∈ S ] ⟦ D s ⟧ X
  ⟦_⟧ `var X = X

  data μ (D : Desc) : Set where
    ⟨_⟩ : ⟦ D ⟧ (μ D) → μ D

  open import Data.Empty
  open import Data.Sum

  `K_`*_ : (S : Set) → Desc → Desc
  `K S `* D = `Σ S (λ _ → D)

  `0 : Desc
  `0 = `Σ ⊥ ⊥-elim

  _`+_ : (A : Desc) → (B : Desc) → Desc
  A `+ B = `Σ (⊤ ⊎ ⊤) (λ { (inj₁ tt) → A ; (inj₂ tt) → B })

  natlist : Desc
  natlist = `Σ (⊤ ⊎ ⊤) (λ { (inj₁ tt) → `1
                          ; (inj₂ tt) → `K ℕ `* `var
                          })

  -- ⟦_⟧ (`Σ S D) X = Σ S λ s → ⟦ D s ⟧ X

-- SPT : 0, 1, ×, +, μ, def, wk, vl, →, fun

data _≃_ (A B : Set) : Set where

open import Function

mutual
  data Desc : Set₁ where
    `1 : Desc
    `K : (S : Set) → Desc
    `var : Desc
    -- _`→_ : (H : Desc) → (D : μ H → Desc) → Desc
    `σ : (n : ℕ)(D : Fin n → Desc) → Desc -- + and 0, could also be done with Σ
    _`×_ : (A B : Desc) → Desc -- First-order product
    `Iso : (C : Desc) → (D : Set) → (D ≃ μ C) → Desc
    `Σ : (S : Desc) → (D : μ S → Desc) → Desc -- We need dependent product. Sadly, the Desc is a Set₁ so we need type-in-type. We can not stratify it because the level can't be used as an index.
  
  ⟦_⟧ : Desc → Set → Set
  ⟦_⟧ `1 X = ⊤
  ⟦_⟧ (`K S) X = S
  ⟦_⟧ `var X = X
  -- ⟦_⟧ (H `→ D) X = (h : μ H) → ⟦ D h ⟧ X
  ⟦_⟧ (`σ n D) X = Σ (Fin n) λ k → ⟦ D k ⟧ X
  ⟦_⟧ (A `× B) X = ⟦ A ⟧ X × ⟦ B ⟧ X
  ⟦_⟧ (`Iso C D i) X = D
  ⟦_⟧ (`Σ S D) X = Σ (μ S) λ s → ⟦ D s ⟧ X
  
  data μ (D : Desc) : Set where
    ⟨_⟩ : ⟦ D ⟧ (μ D) → μ D

record IsSPT (A : Set) : Set₁ where
  field
    desc : Desc
    to : A → μ desc
    from : μ desc → A
    -- should be inverses
