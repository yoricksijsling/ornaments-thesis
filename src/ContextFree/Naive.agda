module ContextFree.Naive where

open import Data.Empty
open import Data.Unit.Base
open import Data.Sum
open import Data.Product
open import Data.Nat

-- Data type as described in 'Generic Programming with Dependent Types'

data Desc : ℕ → Set where
  `0 : ∀{n} → Desc n
  `1 : ∀{n} → Desc n
  _`+_ : ∀{n} → (A B : Desc n) → Desc n
  _`*_ : ∀{n} → (A B : Desc n) → Desc n
  vl : ∀{n} → Desc (suc n)
  wk : ∀{n} → Desc n → Desc (suc n)
  def : ∀{n} → Desc (suc n) → Desc n → Desc n
  `mu : ∀{n} → Desc (suc n) → Desc n

v : ∀{n} k → Desc (k + suc n)
v zero = vl
v (suc k) = wk (v k)

`nat : ∀{n} → Desc n
`nat = `mu (`1 `+ v 0)
`pair : ∀{n} → Desc (2 + n)
`pair = `mu (v 1 `* v 2)
`pair' : ∀{n} → Desc (2 + n)
`pair' = (v 0 `* v 1)

data Tel : ℕ → Set where
  tnil : Tel 0
  tcons : ∀{n} → Desc n → Tel n → Tel (suc n)

-- This interpretation does not terminate
--     ⟦ `nat ⟧ tel ≡ (⊤ ⊎ ⟦ `nat ⟧ tel) ≡ (⊤ ⊎ ⊤ ⊎ ⟦ `nat ⟧ tel) ≡ ...
-- ⟦_⟧ : ∀{n} → Desc n → Tel n → Set
-- ⟦ `0 ⟧ tel = ⊥
-- ⟦ `1 ⟧ tel = ⊤
-- ⟦ A `+ B ⟧ tel = (⟦ A ⟧ tel) ⊎ (⟦ B ⟧ tel)
-- ⟦ A `* B ⟧ tel = (⟦ A ⟧ tel) × (⟦ B ⟧ tel)
-- ⟦_⟧ vl (tcons D tel) = {!!} --⟦ D ⟧ tel
-- ⟦_⟧ (wk D) (tcons _ tel) = ⟦ D ⟧ tel
-- ⟦_⟧ (def F D) tel = ⟦ F ⟧ (tcons D tel)
-- ⟦_⟧ (`mu D) tel = ⟦ D ⟧ (tcons (`mu D) tel)
