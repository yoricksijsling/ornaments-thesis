
module Cx.Extended.Ornament where

open import Common
open import Cx.Extended.Desc public

infixr 3 _⊕_
infixr 4 -⊗_ rec_⊗_ _+⊗_ rec_+⊗_
-- The `u` function tells us how the ornament changes the indices of the current Desc.
-- The `c` function specifies how the context outside the current Desc has changed.
data Orn {I J}(u : Cxf J I) : ∀{Γ Δ dt} (c : Cxf Δ Γ) (D : Desc I Γ dt) → Set₁ where
  ι : ∀{Γ Δ i}{c : Cxf Δ Γ} → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) → Orn u c (ι i)
  -⊗_ : ∀{Γ Δ S xs}{c : Cxf Δ Γ} → (xs⁺ : Orn u (cxf-both c) xs) → Orn u c (S ⊗ xs)
  rec_⊗_ : ∀{Γ Δ i xs}{c : Cxf Δ Γ} →
            (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) → (xs⁺ : Orn u c xs) → Orn u c (rec i ⊗ xs)

  _+⊗_ : ∀{Γ Δ}{c : Cxf Δ Γ}{xs : ConDesc I Γ} →
                (S : (δ : ⟦ Δ ⟧) → Set) → (xs⁺ : Orn u (cxf-forget c S) xs) → Orn u c xs
  rec_+⊗_ : ∀{Γ Δ}{c : Cxf Δ Γ}{xs : ConDesc I Γ} →
                  (j : (δ : ⟦ Δ ⟧) → ⟦ J ⟧) → (xs⁺ : Orn u c xs) → Orn u c xs
  give-K : ∀{Γ Δ S xs}{c : Cxf Δ Γ} →
           (s : (δ : ⟦ Δ ⟧) → S (c δ)) → (xs⁺ : Orn u (cxf-instantiate c s) xs) → Orn u c (S ⊗ xs)

  `0 : ∀{Γ Δ}{c : Cxf Δ Γ} → Orn u c `0
  _⊕_ : ∀{Γ Δ #c x}{c : Cxf Δ Γ}{xs : DatDesc I Γ #c} →
         (x⁺ : Orn u c x) (xs⁺ : Orn u c xs) → Orn u c (x ⊕ xs)

DefOrn : ∀{I}(J : Cx)(u : Cxf J I) {Γ}(Δ : Cx)(c : Cxf Δ Γ) {dt}(D : Desc I Γ dt) → Set₁
DefOrn J u Δ c D = Orn u c D


----------------------------------------
-- Semantics

module _ {I J}{u : Cxf J I} where
  ornToDesc : ∀{Γ Δ dt}{c : Cxf Δ Γ}{D : Desc I Γ dt} → (o : Orn u c D) → Desc J Δ dt
  ornToDesc {c = c} (ι j) = ι (uninv ∘ j)
  ornToDesc (-⊗_ {S = S} {c = c} xs⁺) = S ∘ c ⊗ ornToDesc xs⁺
  ornToDesc (rec j ⊗ xs⁺) = rec (uninv ∘ j) ⊗ ornToDesc xs⁺
  ornToDesc (_+⊗_ S xs⁺) = S ⊗ ornToDesc xs⁺
  ornToDesc (rec_+⊗_ j xs⁺) = rec j ⊗ ornToDesc xs⁺
  ornToDesc (give-K s xs⁺) = ornToDesc xs⁺
  ornToDesc `0 = `0
  ornToDesc (x⁺ ⊕ xs⁺) = ornToDesc x⁺ ⊕ ornToDesc xs⁺

  instance orn-semantics : ∀{Γ Δ dt}{c : Cxf Δ Γ}{D : Desc I Γ dt} → Semantics (Orn u c D)
           orn-semantics = record { ⟦_⟧ = ⟦_⟧ ∘ ornToDesc }


----------------------------------------
-- Identity ornament

idOrn : ∀{I Γ dt}{D : Desc I Γ dt} → Orn id id D
idOrn {dt = isCon} {ι o} = ι (λ δ → inv (o δ))
idOrn {dt = isCon} {S ⊗ xs} = -⊗ idOrn
idOrn {dt = isCon} {rec i ⊗ xs} = rec (λ δ → inv (i δ)) ⊗ idOrn
idOrn {dt = isDat _} {`0} = `0
idOrn {dt = isDat _} {x ⊕ xs} = idOrn ⊕ idOrn


----------------------------------------
-- Ornamental algebra

module _ {I J}{u : Cxf J I} where
  forgetNT : ∀{Γ Δ dt}{c : Cxf Δ Γ}{D : Desc I Γ dt} (o : Orn u c D) →
             ∀ {δ X j} → ⟦ o ⟧ δ (X ∘ u) j → ⟦ D ⟧ (c δ) X (u j)
  forgetNT {c = c} (ι j) {δ} refl = sym (inv-eq (j δ))
  forgetNT (-⊗ xs⁺) (s , v) = s , forgetNT xs⁺ v
  forgetNT (rec j ⊗ xs⁺) {δ} {X} (s , v) = transport X (inv-eq (j δ)) s , forgetNT xs⁺ v
  forgetNT (_+⊗_ S xs⁺) (s , v) = forgetNT xs⁺ v
  forgetNT (rec_+⊗_ j xs⁺) (s , v) = forgetNT xs⁺ v
  forgetNT (give-K s xs⁺) {δ} v = s δ , forgetNT xs⁺ v
  forgetNT `0 (() , _)
  forgetNT (x⁺ ⊕ xs⁺) (zero , v) = zero , forgetNT x⁺ v
  forgetNT (x⁺ ⊕ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

  forgetAlg : ∀{Γ Δ #c}{c : Cxf Δ Γ}{D : DatDesc I Γ #c} (o : Orn u c D) →
              ∀{δ} → Alg (ornToDesc o) δ (μ D (c δ) ∘ u)
  forgetAlg o = ⟨_⟩ ∘ forgetNT o

  forget : ∀{Γ Δ #c}{c : Cxf Δ Γ}{D : DatDesc I Γ #c} (o : Orn u c D) →
           ∀{δ j} → μ (ornToDesc o) δ j → μ D (c δ) (u j)
  forget o = fold (forgetAlg o)
