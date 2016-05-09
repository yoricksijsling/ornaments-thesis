
module Cx.Extended.AlgebraicOrnament where

open import Common
open import Cx.Extended.Ornament public


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
                                            +⊗ rec (λ δ → inv (i (c $ pop δ) , top δ))
                                             ⊗ algOrn′ xs (λ {δ} → curry α (top δ))
  algOrn′ {dt = isDat _} `0 α = `0
  algOrn′ {dt = isDat _} (x ⊕ xs) α = algOrn′ x (curry α 0) ⊕ algOrn′ xs (α ∘ (suc *** id))

  algOrn : ∀{Γ dt}{D : Desc I Γ dt} →
           ({γ : ⟦ Γ ⟧} → Alg D γ J) → DefOrn (I ▷ J) pop Γ id D
  algOrn {D = D} = algOrn′ D


----------------------------------------
-- Composition of ornaments

module _ {I J K}{u : Cxf J I}{v : Cxf K J} where
  compose : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
            (o : Orn u c D) → Orn v d (ornToDesc o) → Orn (u ∘ v) (c ∘ d) D
  compose (ι j) (ι k) = ι (λ _ → inv-∘ (j _) (k _))
  compose (ι j) (T +⊗ ys⁺) = T +⊗ (compose (ι j) ys⁺)
  compose (ι j) (rec k +⊗ ys⁺) = rec k +⊗ (compose (ι j) ys⁺)
  compose (-⊗ xs⁺) (-⊗ ys⁺) = -⊗ (compose xs⁺ ys⁺)
  compose (-⊗ xs⁺) (T +⊗ ys⁺) = T +⊗ (compose (-⊗ xs⁺) ys⁺)
  compose (-⊗ xs⁺) (rec j +⊗ ys⁺) = rec j +⊗ (compose (-⊗ xs⁺) ys⁺)
  compose (-⊗ xs⁺) (give-K t ys⁺) = give-K t (compose xs⁺ ys⁺)
  compose (rec j ⊗ xs⁺) (rec k ⊗ ys⁺) = rec (λ _ → inv-∘ (j _) (k _)) ⊗ compose xs⁺ ys⁺
  compose (rec j ⊗ xs⁺) (T +⊗ ys⁺) = T +⊗ (compose (rec j ⊗ xs⁺) ys⁺)
  compose (rec j ⊗ xs⁺) (rec k +⊗ ys⁺) = rec k +⊗ (compose (rec j ⊗ xs⁺) ys⁺)
  compose {d = d} (S +⊗ xs⁺) (-⊗ ys⁺) = (S ∘ d) +⊗ (compose xs⁺ ys⁺)
  compose (S +⊗ xs⁺) (T +⊗ ys⁺) = T +⊗ (compose (S +⊗ xs⁺) ys⁺)
  compose (S +⊗ xs⁺) (rec k +⊗ ys⁺) = rec k +⊗ (compose (S +⊗ xs⁺) ys⁺)
  compose (S +⊗ xs⁺) (give-K t ys⁺) = compose xs⁺ ys⁺
  compose (rec j +⊗ xs⁺) (rec k ⊗ ys⁺) = rec (uninv ∘ k) +⊗ (compose xs⁺ ys⁺)
  compose (rec j +⊗ xs⁺) (T +⊗ ys⁺) = T +⊗ (compose (rec j +⊗ xs⁺) ys⁺)
  compose (rec j +⊗ xs⁺) (rec k +⊗ ys⁺) = rec k +⊗ (compose (rec j +⊗ xs⁺) ys⁺)
  compose {d = d} (give-K s xs⁺) ys⁺ = give-K (s ∘ d) (compose xs⁺ ys⁺)
  compose `0 `0 = `0
  compose (x⁺ ⊕ xs⁺) (y⁺ ⊕ ys⁺) = (compose x⁺ y⁺) ⊕ (compose xs⁺ ys⁺)

  -- To prove that composition is sound we show that the right description is
  -- returned. The descriptions contain higher order terms so we use
  -- extensionality to compare them.
  module _ (ext : ∀{a b} → Extensionality a b) where
    compose-sound : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
                    (o : Orn u c D) → (p : Orn v d (ornToDesc o)) →
                    (ornToDesc (compose o p)) ≡ ornToDesc p
    compose-sound {d = d} (ι j) (ι k) = cong ι (ext (λ x → uninv-inv-∘ (j (d x)) (k x)))
    compose-sound (ι {i = i} {c} j) (T +⊗ ys⁺) = cong (_⊗_ T) (compose-sound (ι {i = i} {c} j) ys⁺)
    compose-sound (ι {i = i} {c} j) (rec k +⊗ ys⁺) = cong (rec_⊗_ k) (compose-sound (ι {i = i} {c} j) ys⁺)
    compose-sound (-⊗ xs⁺) (-⊗ ys⁺) = cong (_⊗_ _) (compose-sound xs⁺ ys⁺)
    compose-sound (-⊗ xs⁺) (T +⊗ ys⁺) = cong (_⊗_ T) (compose-sound (-⊗ xs⁺) ys⁺)
    compose-sound (-⊗ xs⁺) (rec k +⊗ ys⁺) = cong (rec_⊗_ k) (compose-sound (-⊗ xs⁺) ys⁺)
    compose-sound (-⊗ xs⁺) (give-K t ys⁺) = compose-sound xs⁺ ys⁺
    compose-sound {d = d} (rec j ⊗ xs⁺) (rec k ⊗ ys⁺) =
      cong₂ rec_⊗_ (ext (λ x → uninv-inv-∘ (j (d x)) (k x))) (compose-sound xs⁺ ys⁺)
    compose-sound (rec_⊗_ {i = i} j xs⁺) (T +⊗ ys⁺) = cong (_⊗_ T) (compose-sound (rec_⊗_ {i = i} j xs⁺) ys⁺)
    compose-sound (rec_⊗_ {i = i} j xs⁺) (rec k +⊗ ys⁺) = cong (rec_⊗_ k) (compose-sound (rec_⊗_ {i = i} j xs⁺) ys⁺)
    compose-sound {d = d} (S +⊗ xs⁺) (-⊗ ys⁺) = cong (_⊗_ (S ∘ d)) (compose-sound xs⁺ ys⁺)
    compose-sound (S +⊗ xs⁺) (T +⊗ ys⁺) = cong (_⊗_ T) (compose-sound (S +⊗ xs⁺) ys⁺)
    compose-sound (S +⊗ xs⁺) (rec k +⊗ ys⁺) = cong (rec_⊗_ k) (compose-sound (S +⊗ xs⁺) ys⁺)
    compose-sound (S +⊗ xs⁺) (give-K t ys⁺) = compose-sound xs⁺ ys⁺
    compose-sound (rec j +⊗ xs⁺) (rec k ⊗ ys⁺) = cong (rec_⊗_ (uninv ∘ k)) (compose-sound xs⁺ ys⁺)
    compose-sound (rec j +⊗ xs⁺) (T +⊗ ys⁺) = cong (_⊗_ T) (compose-sound (rec j +⊗ xs⁺) ys⁺)
    compose-sound (rec j +⊗ xs⁺) (rec k +⊗ ys⁺) = cong (rec_⊗_ k) (compose-sound (rec j +⊗ xs⁺) ys⁺)
    compose-sound (give-K s xs⁺) ys⁺ = compose-sound xs⁺ ys⁺
    compose-sound `0 `0 = refl
    compose-sound (x⁺ ⊕ xs⁺) (y⁺ ⊕ ys⁺) = cong₂ _⊕_ (compose-sound x⁺ y⁺) (compose-sound xs⁺ ys⁺)


----------------------------------------
-- Reornaments currently only work when the original datatype does not have
-- parameters. To make it work for all datatypes, the indices have to be
-- dependent on the parameters. (See handwritten notes)
reornament : ∀{I J Δ}{u : Cxf J I}{c : Cxf Δ ε}{#c}{D : DatDesc I ε #c} →
             (o : Orn u c D) → Orn (u ∘ pop) c D
reornament o = compose o (algOrn (λ {δ} → forgetAlg o {δ}))
