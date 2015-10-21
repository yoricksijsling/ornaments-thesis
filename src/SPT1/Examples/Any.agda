module SPT1.Examples.Any (A : Set) where

open import Data.Product
open import Data.Unit
open import Function

open import SPT1.Desc

-- This is a very useless embedding. Made possible by the `Σ constructor.
-- It is probably not really a problem that this is possible. Libraries like
-- regular also allow non-sensical constructions. Because we define the to and
-- from functions ourselves we know how to use and interpret the `Σ correctly.

isSPT-Any : IsSPT A
isSPT-Any = record
  { desc = `Σ A (const `1)
  ; to = λ x → ⟨ x , tt ⟩
  ; from = λ { ⟨ x , tt ⟩ → x }
  }

open import SPT1.Folding isSPT-Any

fold' : ∀{R}(α : A × ⊤ → R) → A → R
fold' = fold
