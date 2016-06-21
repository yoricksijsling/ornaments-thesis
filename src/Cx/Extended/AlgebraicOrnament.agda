
module Cx.Extended.AlgebraicOrnament where

open import Common
open import Cx.Extended.Desc
open import Cx.Extended.Ornament

----------------------------------------
-- Algebraic ornament

module _ {I R} where
  algOrn′ : ∀{Γ Δ dt}{c : Cxf Δ Γ}(D : Desc I Γ dt) →
           (∀{δ : ⟦ Δ ⟧} → Alg D (c δ) R) → Orn (I ▷ R) pop Δ c D
  algOrn′ {dt = isCon} {c = c} (ι o) α = ι (λ δ → inv (o (c δ) , α refl))
  algOrn′ {dt = isCon} (S ⊗ xs) α = -⊗ (algOrn′ xs (λ {γ} → curry α (top γ)))
  algOrn′ {dt = isCon} {c = c} (rec i ⊗ xs) α = R ∘ i ∘ c +⊗
    rec (λ δ → inv (i (c (pop δ)) , top δ)) ⊗
    algOrn′ xs (λ {δ} → curry α (top δ))
  algOrn′ {dt = isDat _} `0 α = `0
  algOrn′ {dt = isDat _} (x ⊕ xs) α = algOrn′ x (curry α 0)
    ⊕ algOrn′ xs (α ∘ (suc *** id))

  algOrn : ∀{Γ dt}(D : Desc I Γ dt) →
           ({γ : ⟦ Γ ⟧} → Alg D γ R) → Orn (I ▷ R) pop Γ id D
  algOrn = algOrn′


----------------------------------------
-- Composition of ornaments

module _ {I J J′}{u : Cxf J I}{v : Cxf J′ J} where
  infixl 9 _>>⁺_
  _>>⁺_ : ∀{Γ Δ Δ′ c d dt} {D : Desc I Γ dt} →
    (o : Orn J u Δ c D) → Orn J′ v Δ′ d (ornToDesc o) →
    Orn J′ (u ∘ v) Δ′ (c ∘ d) D
  _>>⁺_ (ι j) (ι k) = ι (λ _ → inv-∘ (j _) (k _))
  _>>⁺_ (ι j) (T +⊗ ys⁺) = T +⊗ (_>>⁺_ (ι j) ys⁺)
  _>>⁺_ (ι j) (rec k +⊗ ys⁺) = rec k +⊗ (_>>⁺_ (ι j) ys⁺)
  _>>⁺_ (-⊗ xs⁺) (-⊗ ys⁺) = -⊗ (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ (-⊗ xs⁺) (T +⊗ ys⁺) = T +⊗ (_>>⁺_ (-⊗ xs⁺) ys⁺)
  _>>⁺_ (-⊗ xs⁺) (rec j +⊗ ys⁺) = rec j +⊗ (_>>⁺_ (-⊗ xs⁺) ys⁺)
  _>>⁺_ (-⊗ xs⁺) (give-K t ys⁺) = give-K t (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ (rec j ⊗ xs⁺) (rec k ⊗ ys⁺) = rec (λ _ → inv-∘ (j _) (k _)) ⊗ _>>⁺_ xs⁺ ys⁺
  _>>⁺_ (rec j ⊗ xs⁺) (T +⊗ ys⁺) = T +⊗ (_>>⁺_ (rec j ⊗ xs⁺) ys⁺)
  _>>⁺_ (rec j ⊗ xs⁺) (rec k +⊗ ys⁺) = rec k +⊗ (_>>⁺_ (rec j ⊗ xs⁺) ys⁺)
  _>>⁺_ {d = d} (S +⊗ xs⁺) (-⊗ ys⁺) = (S ∘ d) +⊗ (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ (S +⊗ xs⁺) (T +⊗ ys⁺) = T +⊗ (_>>⁺_ (S +⊗ xs⁺) ys⁺)
  _>>⁺_ (S +⊗ xs⁺) (rec k +⊗ ys⁺) = rec k +⊗ (_>>⁺_ (S +⊗ xs⁺) ys⁺)
  _>>⁺_ (S +⊗ xs⁺) (give-K t ys⁺) = _>>⁺_ xs⁺ ys⁺
  _>>⁺_ (rec j +⊗ xs⁺) (rec k ⊗ ys⁺) = rec (uninv ∘ k) +⊗ (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ (rec j +⊗ xs⁺) (T +⊗ ys⁺) = T +⊗ (_>>⁺_ (rec j +⊗ xs⁺) ys⁺)
  _>>⁺_ (rec j +⊗ xs⁺) (rec k +⊗ ys⁺) = rec k +⊗ (_>>⁺_ (rec j +⊗ xs⁺) ys⁺)
  _>>⁺_ {d = d} (give-K s xs⁺) ys⁺ = give-K (s ∘ d) (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ `0 `0 = `0
  _>>⁺_ (x⁺ ⊕ xs⁺) (y⁺ ⊕ ys⁺) = (_>>⁺_ x⁺ y⁺) ⊕ (_>>⁺_ xs⁺ ys⁺)

  module _ (ext : ∀{a b} → Extensionality a b) where
    >>⁺-coherence : ∀{Γ Δ Δ′ c d dt} {D : Desc I Γ dt} →
      (o : Orn J u Δ c D) → (p : Orn J′ v Δ′ d (ornToDesc o)) →
      (ornToDesc (o >>⁺ p)) ≡ ornToDesc p
    >>⁺-coherence {d = d} (ι j) (ι k) = cong ι (ext (λ x → uninv-inv-∘ (j (d x)) (k x)))
    >>⁺-coherence (ι {i = i} j) (T +⊗ ys⁺) = cong (_⊗_ T) (>>⁺-coherence (ι {i = i} j) ys⁺)
    >>⁺-coherence (ι {i = i} j) (rec k +⊗ ys⁺) = cong (rec_⊗_ k) (>>⁺-coherence (ι {i = i} j) ys⁺)
    >>⁺-coherence (-⊗ xs⁺) (-⊗ ys⁺) = cong (_⊗_ _) (>>⁺-coherence xs⁺ ys⁺)
    >>⁺-coherence (-⊗ xs⁺) (T +⊗ ys⁺) = cong (_⊗_ T) (>>⁺-coherence (-⊗ xs⁺) ys⁺)
    >>⁺-coherence (-⊗ xs⁺) (rec k +⊗ ys⁺) = cong (rec_⊗_ k) (>>⁺-coherence (-⊗ xs⁺) ys⁺)
    >>⁺-coherence (-⊗ xs⁺) (give-K t ys⁺) = >>⁺-coherence xs⁺ ys⁺
    >>⁺-coherence {d = d} (rec j ⊗ xs⁺) (rec k ⊗ ys⁺) =
      cong₂ rec_⊗_ (ext (λ x → uninv-inv-∘ (j (d x)) (k x))) (>>⁺-coherence xs⁺ ys⁺)
    >>⁺-coherence (rec_⊗_ {i = i} j xs⁺) (T +⊗ ys⁺) = cong (_⊗_ T) (>>⁺-coherence (rec_⊗_ {i = i} j xs⁺) ys⁺)
    >>⁺-coherence (rec_⊗_ {i = i} j xs⁺) (rec k +⊗ ys⁺) = cong (rec_⊗_ k) (>>⁺-coherence (rec_⊗_ {i = i} j xs⁺) ys⁺)
    >>⁺-coherence {d = d} (S +⊗ xs⁺) (-⊗ ys⁺) = cong (_⊗_ (S ∘ d)) (>>⁺-coherence xs⁺ ys⁺)
    >>⁺-coherence (S +⊗ xs⁺) (T +⊗ ys⁺) = cong (_⊗_ T) (>>⁺-coherence (S +⊗ xs⁺) ys⁺)
    >>⁺-coherence (S +⊗ xs⁺) (rec k +⊗ ys⁺) = cong (rec_⊗_ k) (>>⁺-coherence (S +⊗ xs⁺) ys⁺)
    >>⁺-coherence (S +⊗ xs⁺) (give-K t ys⁺) = >>⁺-coherence xs⁺ ys⁺
    >>⁺-coherence (rec j +⊗ xs⁺) (rec k ⊗ ys⁺) = cong (rec_⊗_ (uninv ∘ k)) (>>⁺-coherence xs⁺ ys⁺)
    >>⁺-coherence (rec j +⊗ xs⁺) (T +⊗ ys⁺) = cong (_⊗_ T) (>>⁺-coherence (rec j +⊗ xs⁺) ys⁺)
    >>⁺-coherence (rec j +⊗ xs⁺) (rec k +⊗ ys⁺) = cong (rec_⊗_ k) (>>⁺-coherence (rec j +⊗ xs⁺) ys⁺)
    >>⁺-coherence (give-K s xs⁺) ys⁺ = >>⁺-coherence xs⁺ ys⁺
    >>⁺-coherence `0 `0 = refl
    >>⁺-coherence (x⁺ ⊕ xs⁺) (y⁺ ⊕ ys⁺) = cong₂ _⊕_ (>>⁺-coherence x⁺ y⁺) (>>⁺-coherence xs⁺ ys⁺)


----------------------------------------
-- Reornament

reornament : ∀{I J u Δ}{c : Cxf Δ ε}{#c}{D : DatDesc I ε #c} →
  (o : Orn J u Δ c D) → Orn (J ▷ μ D tt ∘ u) (u ∘ pop) Δ c D
reornament o = o >>⁺ (algOrn _ (λ {δ} → forgetAlg o {δ}))
