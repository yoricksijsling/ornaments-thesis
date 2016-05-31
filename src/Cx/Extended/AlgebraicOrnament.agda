
module Cx.Extended.AlgebraicOrnament where

open import Common
open import Cx.Extended.Desc
open import Cx.Extended.Ornament

----------------------------------------
-- Algebraic ornament

module _ {I : Cx}{J : Pow ⟦ I ⟧} where
  -- Interestingly, algebraic ornaments only work when the Algebra is
  -- polymorphic in the datatype parameters. That is because during the
  -- definition of datatypes we do not know the values of the parameters, and
  -- by extension we do not know them in an ornament.
  algOrn′ : ∀{Γ Δ dt}{c : Cxf Δ Γ}(D : Desc I Γ dt) →
           (∀{δ : ⟦ Δ ⟧} → Alg D (c δ) J) → DefOrn (I ▷ J) (pop) Δ c D
  algOrn′ {dt = isCon} {c = c} (ι o) α = ι (λ δ → inv (o (c δ) , α refl))
  algOrn′ {dt = isCon} (S ⊗ xs) α = -⊗ (algOrn′ xs (λ {γ} → curry α (top γ)))
  algOrn′ {dt = isCon} {c = c} (rec i ⊗ xs) α = J ∘ i ∘ c
                                            +⊗ rec (λ δ → inv (i (c (pop δ)) , top δ))
                                             ⊗ algOrn′ xs (λ {δ} → curry α (top δ))
  algOrn′ {dt = isDat _} `0 α = `0
  algOrn′ {dt = isDat _} (x ⊕ xs) α = algOrn′ x (curry α 0) ⊕ algOrn′ xs (α ∘ (suc *** id))

  algOrn : ∀{Γ dt}{D : Desc I Γ dt} →
           ({γ : ⟦ Γ ⟧} → Alg D γ J) → DefOrn (I ▷ J) pop Γ id D
  algOrn {D = D} = algOrn′ D


----------------------------------------
-- Composition of ornaments

module _ {I J K}{u : Cxf J I}{v : Cxf K J} where
  infixl 9 _>>⁺_
  _>>⁺_ : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
          (o : Orn u c D) → Orn v d (ornToDesc o) → Orn (u ∘ v) (c ∘ d) D
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

  -- To prove that composition is sound we show that the right description is
  -- returned. The descriptions contain higher order terms so we use
  -- extensionality to compare them.
  module _ (ext : ∀{a b} → Extensionality a b) where
    >>⁺-coherence : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
                    (o : Orn u c D) → (p : Orn v d (ornToDesc o)) →
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
-- Reornaments currently only work when the original datatype does not have
-- parameters. To make it work for all datatypes, the indices have to be
-- dependent on the parameters. (See handwritten notes)
reornament : ∀{I J Δ}{u : Cxf J I}{c : Cxf Δ ε}{#c}{D : DatDesc I ε #c} →
             (o : Orn u c D) → Orn (u ∘ pop) c D
reornament o = o >>⁺ (algOrn (λ {δ} → forgetAlg o {δ}))
