module SPT1.Desc where

open import Data.Product
open import Data.Unit

-- Descriptions of strictly positive types
-- ¿ Closed because they can only refer to themselves ?
--   The indexed version does seem to be open
data Desc : Set₁ where
  `1 : Desc
  `Σ : (S : Set) → (D : S → Desc) → Desc -- A special version of `Σ where S is finite could help us with proofs?
  `var : Desc
  _`→_ : (S : Set) → (D : S → Desc) → Desc
  -- _`×_ : (A B : Desc) → Desc -- Redundant, but first-order

-- Interpret a description as a pattern functor
⟦_⟧ : Desc → Set → Set
⟦_⟧ `1 X = ⊤
⟦_⟧ (`Σ S D) X = Σ[ s ∈ S ] ⟦ D s ⟧ X
⟦_⟧ `var X = X
⟦_⟧ (S `→ D) X = (s : S) → ⟦ D s ⟧ X
-- ⟦_⟧ (A `× B) X = ⟦ A ⟧ X × ⟦ B ⟧ X

-- Fixed point specialised to interpretations of descriptions
data μ (D : Desc) : Set where
  ⟨_⟩ : ⟦ D ⟧ (μ D) → μ D

record IsSPT (A : Set) : Set₁ where
  -- constructor mk
  field
    desc : Desc
    to : A → μ desc
    from : μ desc → A
    -- to and from should be inverses?


-- -------------------------------------------------
-- -- EXAMPLES


-- module NatExample where
--   open import Data.Bool
--   open import Function

--   isDesc-Bool : IsDesc Bool
--   isDesc-Bool = record
--     { desc = `Σ Bool (const `1)
--     ; to = λ x → ⟨ x , tt ⟩
--     ; from = λ { ⟨ x , tt ⟩ → x }
--     }

--   -- foldBool : 
  

-- -- gmap on Desc
-- -- Would gmap on IDesc substitute the indices?

-- -- gmap through IsDesc
