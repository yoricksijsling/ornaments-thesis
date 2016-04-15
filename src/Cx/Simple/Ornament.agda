
module Cx.Simple.Ornament where

open import Common
open import Cx.Simple.Desc public

infixr 3 _⊕_
infixr 4 -⊗_ rec-⊗_ _+⊗_ rec-+⊗_
data ConOrn : ∀{Γ Δ} (f : Cxf Δ Γ) (D : ConDesc Γ) → Set₂ where
  ι : ∀{Γ Δ}{c : Cxf Δ Γ} → ConOrn c ι
  -⊗_ : ∀{Γ Δ S xs}{c : Cxf Δ Γ} → (xs⁺ : ConOrn (cxf-both c) xs) → ConOrn c (S ⊗ xs)
  rec-⊗_ : ∀{Γ Δ xs}{c : Cxf Δ Γ} → (xs⁺ : ConOrn c xs) → ConOrn c (rec-⊗ xs)

  _+⊗_ : ∀{Γ Δ xs}{c : Cxf Δ Γ} →
             (S : (δ : ⟦ Δ ⟧) → Set) → (xs⁺ : ConOrn (cxf-forget c S) xs) → ConOrn c xs
  rec-+⊗_ : ∀{Γ Δ xs}{c : Cxf Δ Γ} → (xs⁺ : ConOrn c xs) → ConOrn c xs

  give-K : ∀{Γ Δ S xs}{c : Cxf Δ Γ} →
           (s : (γ : ⟦ Δ ⟧) → S (Cxf.apply c γ)) → (xs⁺ : ConOrn (cxf-instantiate c s) xs) → ConOrn c (S ⊗ xs)
data DatOrn : ∀{#c}(D : DatDesc #c) → Set₂ where
  `0 : DatOrn `0
  _⊕_ : ∀{#c x xs} → (x⁺ : ConOrn (cxf-id ε) x) (xs⁺ : DatOrn xs) → DatOrn {suc #c} (x ⊕ xs)


----------------------------------------
-- Semantics

conOrnToDesc : ∀{Γ Δ}{c : Cxf Δ Γ}{D : ConDesc Γ} → ConOrn c D → ConDesc Δ
conOrnToDesc ι = ι
conOrnToDesc (-⊗_ {S = S} {c = c} xs⁺) = S ∘ Cxf.apply c ⊗ conOrnToDesc xs⁺
conOrnToDesc (rec-⊗ xs⁺) = rec-⊗ (conOrnToDesc xs⁺)
conOrnToDesc (_+⊗_ S xs⁺) = S ⊗ (conOrnToDesc xs⁺)
conOrnToDesc (rec-+⊗_ xs⁺) = rec-⊗ (conOrnToDesc xs⁺)
conOrnToDesc (give-K s xs⁺) = conOrnToDesc xs⁺
ornToDesc : ∀{#c}{D : DatDesc #c} → DatOrn D → DatDesc #c
ornToDesc `0 = `0
ornToDesc (x⁺ ⊕ xs⁺) = conOrnToDesc x⁺ ⊕ ornToDesc xs⁺

instance conOrn-semantics : ∀{Γ Δ}{c : Cxf Δ Γ}{D : ConDesc Γ} → Semantics (ConOrn c D)
         conOrn-semantics = record { ⟦_⟧ = ⟦_⟧ ∘ conOrnToDesc }
         orn-semantics : ∀{#c}{D : DatDesc #c} → Semantics (DatOrn D)
         orn-semantics = record { ⟦_⟧ = ⟦_⟧ ∘ ornToDesc }

----------------------------------------
-- Ornamental Algebra

conForgetNT : ∀{Γ Δ}{c : Cxf Δ Γ}{D : ConDesc Γ} (o : ConOrn c D) →
              ∀{δ X} → ⟦ o ⟧ δ X → ⟦ D ⟧ (Cxf.apply c δ) X
conForgetNT ι tt = tt
conForgetNT (-⊗ xs⁺) (s , v) = s , conForgetNT xs⁺ v
conForgetNT (rec-⊗ xs⁺) (s , v) = s , conForgetNT xs⁺ v
conForgetNT (_+⊗_ S xs⁺) (s , v) = conForgetNT xs⁺ v
conForgetNT (rec-+⊗_ xs⁺) (s , v) = conForgetNT xs⁺ v
conForgetNT {c = c} (give-K s xs⁺) v = s _ , conForgetNT xs⁺ v
forgetNT : ∀{#c}{D : DatDesc #c} (o : DatOrn D) → ∀{X} → ⟦ o ⟧ X → ⟦ D ⟧ X
forgetNT `0 (() , _)
forgetNT (x⁺ ⊕ xs⁺) (zero , v) = 0 , conForgetNT x⁺ v
forgetNT (x⁺ ⊕ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

forgetAlg : ∀{#c}{D : DatDesc #c} (o : DatOrn D) → DatAlg (ornToDesc o) (μ D)
forgetAlg o = ⟨_⟩ ∘ forgetNT o

forget : ∀{#c}{D : DatDesc #c} (o : DatOrn D) → μ (ornToDesc o) → μ D
forget o = fold (forgetAlg o)
