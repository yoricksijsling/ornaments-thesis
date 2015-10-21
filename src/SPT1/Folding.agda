open import Data.Product
open import Function

open import SPT1.Desc

module SPT1.Folding {Target : Set}(isSPT : IsSPT Target) where

open IsSPT isSPT

Alg : Set → Set
Alg R = ⟦ desc ⟧ R → R

module Fold {R : Set}(α : Alg R) where
  mutual  
    fold : μ desc → R
    fold ⟨ xs ⟩ = α (hyps desc xs)

    hyps : (D' : Desc)(xs : ⟦ D' ⟧ (μ desc)) → ⟦ D' ⟧ R
    hyps `1 tt = tt
    hyps (`Σ S T) (s , xs) = s , hyps (T s) xs
    hyps `var xs = fold xs
    hyps (S `→ T) f s = hyps (T s) (f s)
    -- hyps (A `× B) (a , b) = hyps A a , hyps B b

fold : ∀{R}(α : Alg R) → Target → R
fold α = (Fold.fold α) ∘′ to

