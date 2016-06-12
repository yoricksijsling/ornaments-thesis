
module Cx.Simple.Ornament where

open import Common
open import Cx.Simple.Desc

infixr 2 _⊕_
infixr 3 -⊗_ rec-⊗_ _+⊗_ rec-+⊗_

data ConOrn {Γ Δ} (c : Cxf Δ Γ) : (D : ConDesc Γ) → Set₂ where
  ι : ConOrn c ι
  -⊗_ : ∀{S xs} → (xs⁺ : ConOrn (cxf-both c) xs) → ConOrn c (S ⊗ xs)
  rec-⊗_ : ∀{xs} → (xs⁺ : ConOrn c xs) → ConOrn c (rec-⊗ xs)

  _+⊗_ : ∀{xs} → (S : (δ : ⟦ Δ ⟧) → Set) →
    (xs⁺ : ConOrn (cxf-forget c S) xs) → ConOrn c xs
  rec-+⊗_ : ∀{xs} → (xs⁺ : ConOrn c xs) → ConOrn c xs

  give-K : ∀{S xs} → (s : (γ : ⟦ Δ ⟧) → S (c γ)) →
    (xs⁺ : ConOrn (cxf-inst c s) xs) → ConOrn c (S ⊗ xs)

data DatOrn : ∀{#c}(D : DatDesc #c) → Set₂ where
  `0 : DatOrn `0
  _⊕_ : ∀{#c x xs} →
    (x⁺ : ConOrn id x) (xs⁺ : DatOrn xs) → DatOrn {suc #c} (x ⊕ xs)


----------------------------------------
-- Semantics

conOrnToDesc : ∀{Γ Δ}{c : Cxf Δ Γ}{D : ConDesc Γ} →
               ConOrn c D → ConDesc Δ
conOrnToDesc ι = ι
conOrnToDesc {c = c} (-⊗_ {S = S} xs⁺) = S ∘ c ⊗ conOrnToDesc xs⁺
conOrnToDesc (rec-⊗ xs⁺) = rec-⊗ conOrnToDesc xs⁺
conOrnToDesc (S +⊗ xs⁺) = S ⊗ conOrnToDesc xs⁺
conOrnToDesc (rec-+⊗ xs⁺) = rec-⊗ conOrnToDesc xs⁺
conOrnToDesc (give-K s xs⁺) = conOrnToDesc xs⁺
ornToDesc : ∀{#c}{D : DatDesc #c} → DatOrn D → DatDesc #c
ornToDesc `0 = `0
ornToDesc (x⁺ ⊕ xs⁺) = conOrnToDesc x⁺ ⊕ ornToDesc xs⁺


----------------------------------------
-- Ornamental Algebra

conForgetNT : ∀{Γ Δ}{c : Cxf Δ Γ}{D : ConDesc Γ} →
              (o : ConOrn c D) →
              ∀{δ X} → ⟦ conOrnToDesc o ⟧ δ X → ⟦ D ⟧ (c δ) X
conForgetNT ι tt = tt
conForgetNT (-⊗ xs⁺) (s , v) = s , conForgetNT xs⁺ v
conForgetNT (rec-⊗ xs⁺) (s , v) = s , conForgetNT xs⁺ v
conForgetNT (_+⊗_ S xs⁺) (s , v) = conForgetNT xs⁺ v
conForgetNT (rec-+⊗_ xs⁺) (s , v) = conForgetNT xs⁺ v
conForgetNT (give-K s xs⁺) v = s _ , conForgetNT xs⁺ v
forgetNT : ∀{#c}{D : DatDesc #c} (o : DatOrn D) →
           ∀{X} → ⟦ ornToDesc o ⟧ X → ⟦ D ⟧ X
forgetNT `0 (() , _)
forgetNT (x⁺ ⊕ xs⁺) (zero , v) = 0 , conForgetNT x⁺ v
forgetNT (x⁺ ⊕ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

forgetAlg : ∀{#c}{D : DatDesc #c} (o : DatOrn D) → Alg (ornToDesc o) (μ D)
forgetAlg o = ⟨_⟩ ∘ forgetNT o

forget : ∀{#c}{D : DatDesc #c} (o : DatOrn D) → μ (ornToDesc o) → μ D
forget o = fold (forgetAlg o)
