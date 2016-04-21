module Cx.Simple.Desc where

open import Common
open import Cx.Cx public

infixr 3 _⊕_
infixr 4 _⊗_ rec-⊗_
data ConDesc : Cx₁ → Set₁ where
  ι : ∀{Γ} → ConDesc Γ
  _⊗_ : ∀{Γ}(S : (γ : ⟦ Γ ⟧) → Set) → (xs : ConDesc (Γ ▷ S)) → ConDesc Γ
  rec-⊗_ : ∀{Γ}(xs : ConDesc Γ) → ConDesc Γ
data DatDesc : Nat → Set₁ where
  `0 : DatDesc 0
  _⊕_ : ∀{#c}(x : ConDesc ε)(xs : DatDesc #c) → DatDesc (suc #c)


----------------------------------------
-- Semantics

lookupCtor : ∀{#c}(D : DatDesc #c) → Fin #c → ConDesc ε
lookupCtor `0 ()
lookupCtor (x ⊕ _) zero = x
lookupCtor (_ ⊕ xs) (suc k) = lookupCtor xs k

⟦_⟧conDesc : ∀{Γ} → ConDesc Γ → ⟦ Γ ⟧ → Set → Set
⟦ ι ⟧conDesc γ X = ⊤
⟦ S ⊗ xs ⟧conDesc γ X = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X
⟦ rec-⊗ xs ⟧conDesc γ X = X × ⟦ xs ⟧conDesc γ X
⟦_⟧datDesc : ∀{#c} → DatDesc #c → Set → Set
⟦_⟧datDesc {#c} D X = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc tt X

instance conDesc-semantics : ∀{Γ} → Semantics (ConDesc Γ)
         conDesc-semantics = record { ⟦_⟧ = ⟦_⟧conDesc }
         datDesc-semantics : ∀{#c} → Semantics (DatDesc #c)
         datDesc-semantics = record { ⟦_⟧ = ⟦_⟧datDesc }
{-# DISPLAY ⟦_⟧conDesc x = ⟦_⟧ x #-}
{-# DISPLAY ⟦_⟧datDesc x = ⟦_⟧ x #-}

data μ {#c : Nat}(F : DatDesc #c) : Set where
  ⟨_⟩ : ⟦ F ⟧datDesc (μ F) → μ F


----------------------------------------
-- Folding

DatAlg : ∀{#c} → DatDesc #c → Set → Set
DatAlg D X = ⟦ D ⟧ X → X
ConAlg : ∀{Γ} → ConDesc Γ → ⟦ Γ ⟧ → Set → Set
ConAlg D γ X = ⟦ D ⟧ γ X → X

module Fold {#c}{D : DatDesc #c}{X} (α : DatAlg D X) where
  mutual
    fold : μ D → X
    fold ⟨ xs ⟩ = α (datDescmap-fold D xs) -- D and xs are the starting arguments

    -- Map the fold. It recurses on the description and needs local contexts
    -- to do the mapping. But when the fold is called all this can be
    -- forgotten.
    conDescmap-fold : ∀{Γ′} (D′ : ConDesc Γ′) {γ′} (xs : ⟦ D′ ⟧ γ′ (μ D)) → ⟦ D′ ⟧ γ′ X
    conDescmap-fold ι tt = tt
    conDescmap-fold (S ⊗ xs) (s , v) = s , conDescmap-fold xs v
    conDescmap-fold (rec-⊗ xs) (s , v) = fold s , conDescmap-fold xs v
    datDescmap-fold : ∀{#c} (D′ : DatDesc #c) (xs : ⟦ D′ ⟧ (μ D)) → ⟦ D′ ⟧ X
    datDescmap-fold `0 (() , _)
    datDescmap-fold (x ⊕ xs) (k , v) = k , conDescmap-fold (lookupCtor (x ⊕ xs) k) v
open Fold using (fold) public
