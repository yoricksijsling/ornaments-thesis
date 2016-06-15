
module Cx.Extended.Ornament where

open import Common
open import Cx.Extended.Desc

infixr 2 _⊕_
infixr 3 -⊗_ rec_⊗_ _+⊗_ rec_+⊗_
data Orn {I} J (u : Cxf J I)
  {Γ} Δ (c : Cxf Δ Γ) : ∀{dt}(D : Desc I Γ dt) → Set₁ where
  ι : ∀{i} → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) → Orn _ u _ c (ι i)
  -⊗_ : ∀{S xs} → (xs⁺ : Orn _ u _ (cxf-both c) xs) → Orn _ u _ c (S ⊗ xs)
  rec_⊗_ : ∀{i xs} → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) →
    (xs⁺ : Orn _ u _ c xs) → Orn _ u _ c (rec i ⊗ xs)

  _+⊗_ : ∀{xs : ConDesc I Γ} → (S : (δ : ⟦ Δ ⟧) → Set) →
    (xs⁺ : Orn _ u _ (cxf-forget c S) xs) → Orn _ u _ c xs
  rec_+⊗_ : ∀{xs : ConDesc I Γ} → (j : (δ : ⟦ Δ ⟧) → ⟦ J ⟧) →
    (xs⁺ : Orn _ u _ c xs) → Orn _ u _ c xs
  give-K : ∀{S xs} → (s : (δ : ⟦ Δ ⟧) → S (c δ)) →
    (xs⁺ : Orn _ u _ (cxf-inst c s) xs) → Orn _ u _ c (S ⊗ xs)

  `0 : Orn _ u _ c `0
  _⊕_ : ∀{#c x}{xs : DatDesc I Γ #c} →
    (x⁺ : Orn _ u _ c x) (xs⁺ : Orn _ u _ c xs) → Orn _ u _ c (x ⊕ xs)


----------------------------------------
-- Semantics

module _ {I J u} where
  ornToDesc : ∀{Γ Δ c dt}{D : Desc I Γ dt} →
    (o : Orn J u Δ c D) → Desc J Δ dt
  ornToDesc (ι j) = ι (uninv ∘ j)
  ornToDesc {c = c} (-⊗_ {S = S} xs⁺) = S ∘ c ⊗ ornToDesc xs⁺
  ornToDesc (rec j ⊗ xs⁺) = rec (uninv ∘ j) ⊗ ornToDesc xs⁺
  ornToDesc (_+⊗_ S xs⁺) = S ⊗ ornToDesc xs⁺
  ornToDesc (rec_+⊗_ j xs⁺) = rec j ⊗ ornToDesc xs⁺
  ornToDesc (give-K s xs⁺) = ornToDesc xs⁺
  ornToDesc `0 = `0
  ornToDesc (x⁺ ⊕ xs⁺) = ornToDesc x⁺ ⊕ ornToDesc xs⁺


----------------------------------------
-- Ornamental algebra

module _ {I J u} where
  forgetNT : ∀{Γ Δ c dt}{D : Desc I Γ dt} (o : Orn J u Δ c D) →
             ∀{δ X j} → ⟦ ornToDesc o ⟧ δ (X ∘ u) j → ⟦ D ⟧ (c δ) X (u j)
  forgetNT (ι j) {δ} refl rewrite inv-eq (j δ) = refl
  forgetNT (-⊗ xs⁺) (s , v) = s , forgetNT xs⁺ v
  forgetNT (rec j ⊗ xs⁺) {δ} {X} (s , v) rewrite inv-eq (j δ) = s , forgetNT xs⁺ v
  forgetNT (_+⊗_ S xs⁺) (s , v) = forgetNT xs⁺ v
  forgetNT (rec_+⊗_ j xs⁺) (s , v) = forgetNT xs⁺ v
  forgetNT (give-K s xs⁺) {δ} v = s δ , forgetNT xs⁺ v
  forgetNT `0 (() , _)
  forgetNT (x⁺ ⊕ xs⁺) (zero , v) = zero , forgetNT x⁺ v
  forgetNT (x⁺ ⊕ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

  {-- Almost a full proof that forgetNT is natural
  forgetNT-natural : ∀{Γ Δ c dt}{D : Desc I Γ dt} (o : Orn J u Δ c D) →
    ∀{X Y} (f : X →ⁱ Y) →
    ∀{δ j} → (v : ⟦ ornToDesc o ⟧ δ (X ∘ u) j) →
    forgetNT o (descmap f (ornToDesc o) v)
      ≡ descmap f D (forgetNT o {X = X} v)
  forgetNT-natural (ι j) f refl = refl
  forgetNT-natural (-⊗ xs⁺) f (s , v) = cong (_,_ s) (forgetNT-natural xs⁺ f v)
  forgetNT-natural (rec j ⊗ xs⁺) f {δ} (s , v) rewrite inv-eq (j δ)
    = cong (_,_ (f s)) (forgetNT-natural xs⁺ f v)
  forgetNT-natural (S +⊗ xs⁺) f (s , v) = forgetNT-natural xs⁺ f v
  forgetNT-natural (rec j +⊗ xs⁺) f (s , v) = forgetNT-natural xs⁺ f v
  forgetNT-natural (give-K s xs⁺) f {δ} v = cong (_,_ (s δ)) (forgetNT-natural xs⁺ f v)
  forgetNT-natural `0 f (() , _)
  forgetNT-natural (x⁺ ⊕ xs⁺) f (zero , v) = cong (_,_ zero) (forgetNT-natural x⁺ f v)
  forgetNT-natural (x⁺ ⊕ xs⁺) f (suc k , v) = {!!}
  -}

  forgetAlg : ∀{Γ Δ c #c}{D : DatDesc I Γ #c} (o : Orn J u Δ c D) →
              ∀{δ} → Alg (ornToDesc o) δ (μ D (c δ) ∘ u)
  forgetAlg o = ⟨_⟩ ∘ forgetNT o

  forget : ∀{Γ Δ c #c}{D : DatDesc I Γ #c} (o : Orn J u Δ c D) →
           ∀{δ j} → μ (ornToDesc o) δ j → μ D (c δ) (u j)
  forget o = fold (forgetAlg o)
