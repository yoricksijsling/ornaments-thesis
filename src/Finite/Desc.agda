module Finite.Desc where

open import Data.Empty
open import Data.Unit.Base
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Function

module Finite where
  data Desc : Set where
    `0 : Desc
    `1 : Desc
    _`+_ : (A B : Desc) → Desc
    _`*_ : (A B : Desc) → Desc

  ⟦_⟧ : Desc → Set
  ⟦ `0 ⟧ = ⊥
  ⟦ `1 ⟧ = ⊤
  ⟦ A `+ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
  ⟦ A `* B ⟧ = ⟦ A ⟧ × ⟦ B ⟧

  open import Data.List.Base renaming (map to mapl)

  enum : (d : Desc) → List ⟦ d ⟧
  enum `0 = []
  enum `1 = tt ∷ []
  enum (A `+ B) = mapl inj₁ (enum A) ++ mapl inj₂ (enum B)
  enum (A `* B) = concatMap (λ a → mapl (λ b → a , b) (enum B)) (enum A)

module FiniteDependent where
  mutual
    data Desc : Set where
      `0 : Desc
      `1 : Desc
      _`+_ : (A B : Desc) → Desc
      _`*_ : (A : Desc)(B : ⟦ A ⟧ → Desc) → Desc

    ⟦_⟧ : Desc → Set
    ⟦ `0 ⟧ = ⊥
    ⟦ `1 ⟧ = ⊤
    ⟦ A `+ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
    ⟦ A `* B ⟧ = Σ ⟦ A ⟧ (λ x → ⟦ B x ⟧)
