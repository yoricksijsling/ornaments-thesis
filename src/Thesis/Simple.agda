module Thesis.Simple where

open import Common
open import Cx.Simple

listDesc : (A : Set) → DatDesc 2
listDesc A = ι ⊕ ((λ γ → A) ⊗ rec-⊗ ι) ⊕ `0

-- listDesc-nil : ∀{A} → μ (listDesc A)
-- listDesc-nil = ⟨ 0 , tt ⟩

-- listDesc-cons : ∀{A} → A → μ (listDesc A) → μ (listDesc A)
-- listDesc-cons x xs = ⟨ 1 , x , xs , tt ⟩

-- (n : Nat) → Fin n → AnyFin
anyFin : DatDesc 1
anyFin = (λ γ → Nat) ⊗ (λ γ → Fin (top γ)) ⊗ ι ⊕ `0


pairDesc : (A : Set) (B : A → Set) → DatDesc 1
pairDesc A B = ((λ γ → A) ⊗ (λ γ → B (top γ)) ⊗ ι) ⊕ `0

pair-to : {A : Set}{B : A → Set} → Σ A B → μ (pairDesc A B)
pair-to (x , y) = ⟨ 0 , x , y , tt ⟩

{-
fold : ∀{#c}{D : DatDesc #c}{X} (α : DatAlg D X) →
       μ D → X
fold {D = D} α ⟨ xs ⟩ = α (datDescmap (fold α) D xs)
-}
