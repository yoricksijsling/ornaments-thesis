open import SPT.Desc

module SPT.Folding {Target : Set}{{isSPT : IsSPT Target}} where

open import Data.Product
open import Function

open IsSPT isSPT

Alg : Set → Set
Alg R = ⟦ desc ⟧ R → R

module Fold {R : Set}(α : Alg R) where
  mutual
    fold : μ desc → R
    fold ⟨ xs ⟩ = α (hyps desc xs)

    hyps : (D' : Desc)(xs : ⟦ D' ⟧ (μ desc)) → ⟦ D' ⟧ R
    hyps `1 tt = tt
    hyps (`K S) xs = xs
    hyps (`Σ S D') (s , xs) = s , hyps (D' s) xs
    hyps `var xs = fold xs
    hyps (`σ n D') (k , xs) = k , hyps (D' k) xs
    hyps (A `× B) (a , b) = hyps A a , hyps B b

fold : ∀{R}(α : Alg R) → Target → R
fold α = Fold.fold α ∘′ to
