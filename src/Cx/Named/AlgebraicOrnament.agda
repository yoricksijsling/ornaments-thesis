
module Cx.Named.AlgebraicOrnament where

open import Common
open import Cx.Named.Ornament public


----------------------------------------
-- Algebraic ornament

module _ {I R} where
  algOrn′ : ∀{Γ Δ dt}{c : Cxf Δ Γ}(D : Desc I Γ dt) →
           (∀{δ : ⟦ Δ ⟧} → Alg D (c δ) R) → Orn (I ▷ R) pop Δ c D
  algOrn′ {dt = isCon} {c = c} (ι o) α = ι (λ δ → inv (o (c δ) , α refl))
  algOrn′ {dt = isCon} (nm / S ⊗ xs) α = nm /-⊗ (algOrn′ xs (λ {γ} → curry α (top γ)))
  algOrn′ {dt = isCon} {c = c} (nm /rec i ⊗ xs) α = "_" / (R ∘ i ∘ c)
                                                 +⊗ nm /rec (λ δ → inv (i (c $ pop δ) , top δ))
                                                  ⊗ algOrn′ xs (λ {δ} → curry α (top δ))
  algOrn′ {dt = isDat _} `0 α = `0
  algOrn′ {dt = isDat _} (x ⊕ xs) α = algOrn′ x (curry α 0) ⊕ algOrn′ xs (α ∘ (suc *** id))

  algOrn : ∀{Γ dt}{D : Desc I Γ dt} →
           ({γ : ⟦ Γ ⟧} → Alg D γ R) → Orn (I ▷ R) pop Γ id D
  algOrn {D = D} = algOrn′ D


----------------------------------------
-- Composition of ornaments

module _ {I J J′}{u : Cxf J I}{v : Cxf J′ J} where
  infixl 9 _>>⁺_
  _>>⁺_ : ∀{Γ Δ Δ′ c d dt} {D : Desc I Γ dt} →
    (o : Orn J u Δ c D) → Orn J′ v Δ′ d (ornToDesc o) →
    Orn J′ (u ∘ v) Δ′ (c ∘ d) D
  _>>⁺_ (ι j) (ι k) = ι (λ _ → inv-∘ (j _) (k _))
  _>>⁺_ (ι j) (nm / T +⊗ ys⁺) = nm / T +⊗ (_>>⁺_ (ι j) ys⁺)
  _>>⁺_ (ι j) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (_>>⁺_ (ι j) ys⁺)
  _>>⁺_ (nm′ /-⊗ xs⁺) (nm /-⊗ ys⁺) = nm /-⊗ (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ (nm′ /-⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (_>>⁺_ (nm′ /-⊗ xs⁺) ys⁺)
  _>>⁺_ (nm′ /-⊗ xs⁺) (nm /rec j +⊗ ys⁺) = nm /rec j +⊗ (_>>⁺_ (nm′ /-⊗ xs⁺) ys⁺)
  _>>⁺_ (nm′ /-⊗ xs⁺) (give-K t ys⁺) = give-K t (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ (nm′ /rec j ⊗ xs⁺) (nm /rec k ⊗ ys⁺) = nm /rec (λ _ → inv-∘ (j _) (k _)) ⊗ _>>⁺_ xs⁺ ys⁺
  _>>⁺_ (nm′ /rec j ⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (_>>⁺_ (nm′ /rec j ⊗ xs⁺) ys⁺)
  _>>⁺_ (nm′ /rec j ⊗ xs⁺) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (_>>⁺_ (nm′ /rec j ⊗ xs⁺) ys⁺)
  _>>⁺_ {d = d} (nm′ / S +⊗ xs⁺) (nm /-⊗ ys⁺) = nm / (S ∘ d) +⊗ (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ (nm′ / S +⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (_>>⁺_ (nm′ / S +⊗ xs⁺) ys⁺)
  _>>⁺_ (nm′ / S +⊗ xs⁺) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (_>>⁺_ (nm′ / S +⊗ xs⁺) ys⁺)
  _>>⁺_ (nm′ / S +⊗ xs⁺) (give-K t ys⁺) = _>>⁺_ xs⁺ ys⁺
  _>>⁺_ (nm′ /rec j +⊗ xs⁺) (nm /rec k ⊗ ys⁺) = nm /rec (uninv ∘ k) +⊗ (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ (nm′ /rec j +⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (_>>⁺_ (nm′ /rec j +⊗ xs⁺) ys⁺)
  _>>⁺_ (nm′ /rec j +⊗ xs⁺) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (_>>⁺_ (nm′ /rec j +⊗ xs⁺) ys⁺)
  _>>⁺_ {d = d} (give-K s xs⁺) ys⁺ = give-K (s ∘ d) (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ `0 `0 = `0
  _>>⁺_ (x⁺ ⊕ xs⁺) (y⁺ ⊕ ys⁺) = (_>>⁺_ x⁺ y⁺) ⊕ (_>>⁺_ xs⁺ ys⁺)

  module _ (ext : ∀{a b} → Extensionality a b) where
    >>⁺-coherence : ∀{Γ Δ Δ′ c d dt} {D : Desc I Γ dt} →
      (o : Orn J u Δ c D) → (p : Orn J′ v Δ′ d (ornToDesc o)) →
      (ornToDesc (o >>⁺ p)) ≡ ornToDesc p
    >>⁺-coherence {d = d} (ι j) (ι k) = cong ι (ext (λ x → uninv-inv-∘ (j (d x)) (k x)))
    >>⁺-coherence (ι {i = i} j) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (>>⁺-coherence (ι {i = i} j) ys⁺)
    >>⁺-coherence (ι {i = i} j) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (>>⁺-coherence (ι {i = i} j) ys⁺)
    >>⁺-coherence (nm′ /-⊗ xs⁺) (nm /-⊗ ys⁺) = cong (_/_⊗_ _ _) (>>⁺-coherence xs⁺ ys⁺)
    >>⁺-coherence (nm′ /-⊗ xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (>>⁺-coherence (nm′ /-⊗ xs⁺) ys⁺)
    >>⁺-coherence (nm′ /-⊗ xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (>>⁺-coherence (nm′ /-⊗ xs⁺) ys⁺)
    >>⁺-coherence (nm′ /-⊗ xs⁺) (give-K t ys⁺) = >>⁺-coherence xs⁺ ys⁺
    >>⁺-coherence {d = d} (nm′ /rec j ⊗ xs⁺) (nm /rec k ⊗ ys⁺) =
      cong₂ (_/rec_⊗_ _) (ext (λ x → uninv-inv-∘ (j (d x)) (k x))) (>>⁺-coherence xs⁺ ys⁺)
    >>⁺-coherence (_/rec_⊗_ {i = i} nm′ j xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (>>⁺-coherence (_/rec_⊗_ {i = i} nm′ j xs⁺) ys⁺)
    >>⁺-coherence (_/rec_⊗_ {i = i} nm′ j xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (>>⁺-coherence (_/rec_⊗_ {i = i} nm′ j xs⁺) ys⁺)
    >>⁺-coherence {d = d} (nm′ / S +⊗ xs⁺) (nm /-⊗ ys⁺) = cong (_/_⊗_ nm (S ∘ d)) (>>⁺-coherence xs⁺ ys⁺)
    >>⁺-coherence (nm′ / S +⊗ xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (>>⁺-coherence (nm′ / S +⊗ xs⁺) ys⁺)
    >>⁺-coherence (nm′ / S +⊗ xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (>>⁺-coherence (nm′ / S +⊗ xs⁺) ys⁺)
    >>⁺-coherence (nm′ / S +⊗ xs⁺) (give-K t ys⁺) = >>⁺-coherence xs⁺ ys⁺
    >>⁺-coherence (nm′ /rec j +⊗ xs⁺) (nm /rec k ⊗ ys⁺) = cong (_/rec_⊗_ nm (uninv ∘ k)) (>>⁺-coherence xs⁺ ys⁺)
    >>⁺-coherence (nm′ /rec j +⊗ xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (>>⁺-coherence (nm′ /rec j +⊗ xs⁺) ys⁺)
    >>⁺-coherence (nm′ /rec j +⊗ xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (>>⁺-coherence (nm′ /rec j +⊗ xs⁺) ys⁺)
    >>⁺-coherence (give-K s xs⁺) ys⁺ = >>⁺-coherence xs⁺ ys⁺
    >>⁺-coherence `0 `0 = refl
    >>⁺-coherence (x⁺ ⊕ xs⁺) (y⁺ ⊕ ys⁺) = cong₂ _⊕_ (>>⁺-coherence x⁺ y⁺) (>>⁺-coherence xs⁺ ys⁺)


----------------------------------------
-- Reornaments currently only work when the original datatype does not have
-- parameters. To make it work for all datatypes, the indices have to be
-- dependent on the parameters. (See handwritten notes)

reornament : ∀{I J u Δ}{c : Cxf Δ ε}{#c}{D : DatDesc I ε #c} →
  (o : Orn J u Δ c D) → Orn (J ▷ μ D tt ∘ u) (u ∘ pop) Δ c D
reornament o = o >>⁺ (algOrn (λ {δ} → forgetAlg o {δ}))
