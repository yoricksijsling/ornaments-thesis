
module Cx.Named.Ornament where

open import Common
open import Cx.Named.Desc public

infixr 2 _⊕_
infixr 3 _/-⊗_ _/rec_⊗_ _/_+⊗_ _/rec_+⊗_
data Orn {I} J (u : Cxf J I)
  {Γ} Δ (c : Cxf Δ Γ) : ∀{dt}(D : Desc I Γ dt) → Set₁ where
  ι : ∀{i} → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) → Orn _ u _ c (ι i)
  _/-⊗_ : ∀{nm S xs} (nm′ : String) →
    (xs⁺ : Orn _ u _ (cxf-both c) xs) → Orn _ u _ c (nm / S ⊗ xs)
  _/rec_⊗_ : ∀{nm i xs} (nm′ : String) → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) →
    (xs⁺ : Orn _ u _ c xs) → Orn _ u _ c (nm /rec i ⊗ xs)

  _/_+⊗_ : {xs : ConDesc I Γ} (nm : String) (S : (δ : ⟦ Δ ⟧) → Set)
    (xs⁺ : Orn _ u _ (cxf-forget c S) xs) → Orn _ u _ c xs
  _/rec_+⊗_ : {xs : ConDesc I Γ} (nm : String) (j : (δ : ⟦ Δ ⟧) → ⟦ J ⟧)
    (xs⁺ : Orn _ u _ c xs) → Orn _ u _ c xs
  give-K : ∀{S xs nm} → (s : (δ : ⟦ Δ ⟧) → S (c δ)) →
    (xs⁺ : Orn _ u _ (cxf-inst c s) xs) → Orn _ u _ c (nm / S ⊗ xs)

  `0 : Orn _ u _ c `0
  _⊕_ : ∀{#c x}{xs : DatDesc I Γ #c}
    (x⁺ : Orn _ u _ c x) (xs⁺ : Orn _ u _ c xs) → Orn _ u _ c (x ⊕ xs)


----------------------------------------
-- Semantics

module _ {I J u} where
  ornToDesc : ∀{Γ Δ c dt}{D : Desc I Γ dt} →
    (o : Orn J u Δ c D) → Desc J Δ dt
  ornToDesc (ι j) = ι (uninv ∘ j)
  ornToDesc {c = c} (_/-⊗_ {S = S} nm xs⁺) = nm / S ∘ c ⊗ ornToDesc xs⁺
  ornToDesc (_/rec_⊗_ nm j xs⁺) = nm /rec (uninv ∘ j) ⊗ ornToDesc xs⁺
  ornToDesc (_/_+⊗_ nm S xs⁺) = nm / S ⊗ ornToDesc xs⁺
  ornToDesc (_/rec_+⊗_ nm j xs⁺) = nm /rec j ⊗ ornToDesc xs⁺
  ornToDesc (give-K s xs⁺) = ornToDesc xs⁺
  ornToDesc `0 = `0
  ornToDesc (_⊕_ x⁺ xs⁺) = ornToDesc x⁺ ⊕ ornToDesc xs⁺


----------------------------------------
-- Ornamental algebra

module _ {I J u} where
  forgetNT : ∀{Γ Δ c dt}{D : Desc I Γ dt} (o : Orn J u Δ c D) →
             ∀{δ X j} → ⟦ ornToDesc o ⟧ δ (X ∘ u) j → ⟦ D ⟧ (c δ) X (u j)
  forgetNT {c = c} (ι j) {δ} refl = sym (inv-eq (j δ))
  forgetNT (_/-⊗_ _ xs⁺) (s , v) = s , forgetNT xs⁺ v
  forgetNT (_/rec_⊗_ _ j xs⁺) {δ} {X} (s , v) = transport X (inv-eq (j δ)) s , forgetNT xs⁺ v
  forgetNT (_/_+⊗_ _ _ xs⁺) (_ , v) = forgetNT xs⁺ v
  forgetNT (_/rec_+⊗_ _ _ xs⁺) (_ , v) = forgetNT xs⁺ v
  forgetNT (give-K s xs⁺) {δ} v = s δ , forgetNT xs⁺ v
  forgetNT `0 (() , _)
  forgetNT (x⁺ ⊕ xs⁺) (zero , v) = zero , forgetNT x⁺ v
  forgetNT (x⁺ ⊕ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

  forgetAlg : ∀{Γ Δ c #c}{D : DatDesc I Γ #c} (o : Orn J u Δ c D) →
              ∀{δ} → Alg (ornToDesc o) δ (μ D (c δ) ∘ u)
  forgetAlg o = ⟨_⟩ ∘ forgetNT o

  forget : ∀{Γ Δ c #c}{D : DatDesc I Γ #c} (o : Orn J u Δ c D) →
           ∀{δ j} → μ (ornToDesc o) δ j → μ D (c δ) (u j)
  forget o = fold (forgetAlg o)
