module Cx.Simple.Desc where

open import Common
open import Cx.Cx public

infixr 2 _⊕_
infixr 3 _⊗_ rec-⊗_
data ConDesc (Γ : Cx₁) : Set₁ where
  ι : ConDesc Γ
  _⊗_ : (S : (γ : ⟦ Γ ⟧) → Set) → (xs : ConDesc (Γ ▷ S)) → ConDesc Γ
  rec-⊗_ : (xs : ConDesc Γ) → ConDesc Γ
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
-- Map

conDescmap : ∀{Γ X Y} (f : X → Y) (D : ConDesc Γ) →
             ∀{γ} → (v : ⟦ D ⟧ γ X) → ⟦ D ⟧ γ Y
conDescmap f ι tt = tt
conDescmap f (S ⊗ xs) (s , v) = s , conDescmap f xs v
conDescmap f (rec-⊗ xs) (s , v) = f s , conDescmap f xs v

datDescmap : ∀{#c X Y} (f : X → Y) (D : DatDesc #c) →
             (v : ⟦ D ⟧ X) → ⟦ D ⟧ Y
datDescmap f xs (k , v) = k , conDescmap f (lookupCtor xs k) v


----------------------------------------
-- Folding

Alg : ∀{#c} → DatDesc #c → Set → Set
Alg D X = ⟦ D ⟧ X → X

module Fold {#c}{D : DatDesc #c}{X} (α : Alg D X) where
  mutual
    fold : μ D → X
    fold ⟨ xs ⟩ = α (datDescmap-fold D xs) -- D and xs are the starting arguments

    -- Map the fold. It recurses on the description and needs local contexts
    -- to do the mapping. But when the fold is called all this can be
    -- forgotten.
    conDescmap-fold : ∀{Γ′} (D′ : ConDesc Γ′) {γ′} → ⟦ D′ ⟧ γ′ (μ D) → ⟦ D′ ⟧ γ′ X
    conDescmap-fold ι tt = tt
    conDescmap-fold (S ⊗ xs) (s , v) = s , conDescmap-fold xs v
    conDescmap-fold (rec-⊗ xs) (s , v) = fold s , conDescmap-fold xs v
    datDescmap-fold : ∀{#c} (D′ : DatDesc #c) (xs : ⟦ D′ ⟧ (μ D)) → ⟦ D′ ⟧ X
    datDescmap-fold xs (k , v) = k , conDescmap-fold (lookupCtor xs k) v
open Fold using (fold) public
