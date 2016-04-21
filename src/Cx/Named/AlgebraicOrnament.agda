
module Cx.Named.AlgebraicOrnament where

open import Common
open import Cx.Named.Ornament public


----------------------------------------
-- Algebraic ornament

module _ {I : Cx}{J : Pow ⟦ I ⟧} where
  -- Interestingly, algebraic ornaments only work when the Algebra is
  -- polymorphic in the datatype parameters. That is because during the
  -- definition of datatypes we do not know the values of the parameters, and
  -- by extension we do not know them in an ornament.
  algOrn : ∀{Γ Δ dt}{c : Cxf Δ Γ}(D : Desc I Γ dt) →
           (∀{δ : ⟦ Δ ⟧} → Alg D (c $$ δ) J) → DefOrn (I ▷ J) (mk pop) Δ c D
  algOrn {dt = isCon} {c = c} (ι o) α = ι (λ δ → inv (o (c $$ δ) , α refl))
  algOrn {dt = isCon} (nm / S ⊗ xs) α = nm /-⊗ (algOrn xs (λ {γ} → curry α (top γ)))
  algOrn {dt = isCon} {c = c} (nm /rec i ⊗ xs) α = "_" / (J ∘ i ∘ _$$_ c)
                                                +⊗ nm /rec (λ δ → inv (i (c $$ pop δ) , top δ))
                                                 ⊗ algOrn xs (λ {δ} → curry α (top δ))
  algOrn {dt = isDat _} `0 α = `0
  algOrn {dt = isDat _} (x ⊕ xs) α = algOrn x (curry α 0) ⊕ algOrn xs (α ∘ (suc *** id))


----------------------------------------
-- Composition of ornaments

module _ {I J K}{u : Cxf J I}{v : Cxf K J} where
  compose : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
            (o : Orn u c D) → Orn v d (ornToDesc o) → Orn (cxf-∘ u v) (cxf-∘ c d) D
  compose (ι j) (ι k) = ι (λ _ → inv-∘ (j _) (k _))
  compose (ι j) (nm / T +⊗ ys⁺) = nm / T +⊗ (compose (ι j) ys⁺)
  compose (ι j) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (compose (ι j) ys⁺)
  compose (nm′ /-⊗ xs⁺) (nm /-⊗ ys⁺) = nm /-⊗ (compose xs⁺ ys⁺)
  compose (nm′ /-⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (compose (nm′ /-⊗ xs⁺) ys⁺)
  compose (nm′ /-⊗ xs⁺) (nm /rec j +⊗ ys⁺) = nm /rec j +⊗ (compose (nm′ /-⊗ xs⁺) ys⁺)
  compose (nm′ /-⊗ xs⁺) (give-K t ys⁺) = give-K t (compose xs⁺ ys⁺)
  compose (nm′ /rec j ⊗ xs⁺) (nm /rec k ⊗ ys⁺) = nm /rec (λ _ → inv-∘ (j _) (k _)) ⊗ compose xs⁺ ys⁺
  compose (nm′ /rec j ⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (compose (nm′ /rec j ⊗ xs⁺) ys⁺)
  compose (nm′ /rec j ⊗ xs⁺) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (compose (nm′ /rec j ⊗ xs⁺) ys⁺)
  compose {d = d} (nm′ / S +⊗ xs⁺) (nm /-⊗ ys⁺) = nm / (S ∘ _$$_ d) +⊗ (compose xs⁺ ys⁺)
  compose (nm′ / S +⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (compose (nm′ / S +⊗ xs⁺) ys⁺)
  compose (nm′ / S +⊗ xs⁺) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (compose (nm′ / S +⊗ xs⁺) ys⁺)
  compose (nm′ / S +⊗ xs⁺) (give-K t ys⁺) = compose xs⁺ ys⁺
  compose (nm′ /rec j +⊗ xs⁺) (nm /rec k ⊗ ys⁺) = nm /rec (uninv ∘ k) +⊗ (compose xs⁺ ys⁺)
  compose (nm′ /rec j +⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (compose (nm′ /rec j +⊗ xs⁺) ys⁺)
  compose (nm′ /rec j +⊗ xs⁺) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (compose (nm′ /rec j +⊗ xs⁺) ys⁺)
  compose {d = d} (give-K s xs⁺) ys⁺ = give-K (s ∘ _$$_ d) (compose xs⁺ ys⁺)
  compose `0 `0 = `0
  compose (x⁺ ⊕ xs⁺) (y⁺ ⊕ ys⁺) = (compose x⁺ y⁺) ⊕ (compose xs⁺ ys⁺)

  -- To prove that composition is sound we show that the right description is
  -- returned. The descriptions contain higher order terms so we use
  -- extensionality to compare them.
  module _ (ext : ∀{a b} → Extensionality a b) where
    compose-sound : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
                    (o : Orn u c D) → (p : Orn v d (ornToDesc o)) →
                    (ornToDesc (compose o p)) ≡ ornToDesc p
    compose-sound {d = d} (ι j) (ι k) = cong ι (ext (λ x → uninv-inv-∘ (j (d $$ x)) (k x)))
    compose-sound (ι {i = i} {c} j) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (compose-sound (ι {i = i} {c} j) ys⁺)
    compose-sound (ι {i = i} {c} j) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (compose-sound (ι {i = i} {c} j) ys⁺)
    compose-sound (nm′ /-⊗ xs⁺) (nm /-⊗ ys⁺) = cong (_/_⊗_ _ _) (compose-sound xs⁺ ys⁺)
    compose-sound (nm′ /-⊗ xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (compose-sound (nm′ /-⊗ xs⁺) ys⁺)
    compose-sound (nm′ /-⊗ xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (compose-sound (nm′ /-⊗ xs⁺) ys⁺)
    compose-sound (nm′ /-⊗ xs⁺) (give-K t ys⁺) = compose-sound xs⁺ ys⁺
    compose-sound {d = d} (nm′ /rec j ⊗ xs⁺) (nm /rec k ⊗ ys⁺) =
      cong₂ (_/rec_⊗_ _) (ext (λ x → uninv-inv-∘ (j (d $$ x)) (k x))) (compose-sound xs⁺ ys⁺)
    compose-sound (_/rec_⊗_ {i = i} nm′ j xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (compose-sound (_/rec_⊗_ {i = i} nm′ j xs⁺) ys⁺)
    compose-sound (_/rec_⊗_ {i = i} nm′ j xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (compose-sound (_/rec_⊗_ {i = i} nm′ j xs⁺) ys⁺)
    compose-sound {d = d} (nm′ / S +⊗ xs⁺) (nm /-⊗ ys⁺) = cong (_/_⊗_ nm (S ∘ _$$_ d)) (compose-sound xs⁺ ys⁺)
    compose-sound (nm′ / S +⊗ xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (compose-sound (nm′ / S +⊗ xs⁺) ys⁺)
    compose-sound (nm′ / S +⊗ xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (compose-sound (nm′ / S +⊗ xs⁺) ys⁺)
    compose-sound (nm′ / S +⊗ xs⁺) (give-K t ys⁺) = compose-sound xs⁺ ys⁺
    compose-sound (nm′ /rec j +⊗ xs⁺) (nm /rec k ⊗ ys⁺) = cong (_/rec_⊗_ nm (uninv ∘ k)) (compose-sound xs⁺ ys⁺)
    compose-sound (nm′ /rec j +⊗ xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (compose-sound (nm′ /rec j +⊗ xs⁺) ys⁺)
    compose-sound (nm′ /rec j +⊗ xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (compose-sound (nm′ /rec j +⊗ xs⁺) ys⁺)
    compose-sound (give-K s xs⁺) ys⁺ = compose-sound xs⁺ ys⁺
    compose-sound `0 `0 = refl
    compose-sound (x⁺ ⊕ xs⁺) (y⁺ ⊕ ys⁺) = cong₂ _⊕_ (compose-sound x⁺ y⁺) (compose-sound xs⁺ ys⁺)


----------------------------------------
-- Reornaments currently only work when the original datatype does not have
-- parameters. To make it work for all datatypes, the indices have to be
-- dependent on the parameters. (See handwritten notes)

reornament : ∀{I J Δ}{u : Cxf J I}{c : Cxf Δ ε}{#c}{D : DatDesc I ε #c} →
             (o : Orn u c D) → Orn (cxf-∘ u (mk pop)) c D
reornament o = compose o (algOrn (ornToDesc o) (λ {δ} → forgetAlg o {δ}))
