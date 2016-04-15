
module Cx.Named.AlgebraicOrnament where

open import Common
open import Cx.Named.Ornament public


----------------------------------------
-- Algebraic ornament

module _ {I : Set}{J : I → Set} where
  -- Interestingly, algebraic ornaments only work when the Algebra is
  -- polymorphic in the datatype parameters. That is because during the
  -- definition of datatypes we do not know the values of the parameters, and
  -- by extension we do not know them in an ornament.
  algOrn : ∀{Γ Δ dt}{c : Cxf Δ Γ}(D : Desc I Γ dt) →
           (∀{δ : ⟦ Δ ⟧} → Alg D (apply c δ) J) → DefOrn (Σ I J) fst Δ c D
  algOrn {dt = isCon} {c = c} (ι o) α = ι (λ δ → inv (o (apply c δ) , α refl))
  algOrn {dt = isCon} (nm / S ⊗ xs) α = -⊗ (algOrn xs (λ {γ} → curry α (top γ)))
  algOrn {dt = isCon} {c = c} (nm /rec i ⊗ xs) α = "_" / (J ∘ i ∘ apply c)
                                                +⊗ rec (λ δ → inv (i (apply c (pop δ)) , top δ))
                                                 ⊗ algOrn xs (λ {δ} → curry α (top δ))
  algOrn {dt = isDat _} `0 α = `0
  algOrn {dt = isDat _} (nm ∣ x ⊕ xs) α = id ∣ algOrn x (curry α 0) ⊕ algOrn xs (α ∘ (suc *** id))


----------------------------------------
-- Composition of ornaments

module _ {I J K : Set}{u : J → I}{v : K → J} where
  compose : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
            (o : Orn u c D) → Orn v d (ornToDesc o) → Orn (u ∘ v) (cxf-∘ c d) D
  compose (ι j) (ι k) = ι (λ _ → inv-∘ (j _) (k _))
  compose (ι j) (nm / T +⊗ ys⁺) = nm / T +⊗ (compose (ι j) ys⁺)
  compose (ι j) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (compose (ι j) ys⁺)
  compose (-⊗ xs⁺) (-⊗ ys⁺) = -⊗ (compose xs⁺ ys⁺)
  compose (-⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (compose (-⊗ xs⁺) ys⁺)
  compose (-⊗ xs⁺) (nm /rec j +⊗ ys⁺) = nm /rec j +⊗ (compose (-⊗ xs⁺) ys⁺)
  compose (-⊗ xs⁺) (give-K t ys⁺) = give-K t (compose xs⁺ ys⁺)
  compose (rec j ⊗ xs⁺) (rec k ⊗ ys⁺) = rec (λ _ → inv-∘ (j _) (k _)) ⊗ compose xs⁺ ys⁺
  compose (rec j ⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (compose (rec j ⊗ xs⁺) ys⁺)
  compose (rec j ⊗ xs⁺) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (compose (rec j ⊗ xs⁺) ys⁺)
  compose {d = d} (nm / S +⊗ xs⁺) (-⊗ ys⁺) = nm / (S ∘ apply d) +⊗ (compose xs⁺ ys⁺)
  compose (nm / S +⊗ xs⁺) (nm2 / T +⊗ ys⁺) = nm2 / T +⊗ (compose (nm / S +⊗ xs⁺) ys⁺)
  compose (nm / S +⊗ xs⁺) (nm2 /rec k +⊗ ys⁺) = nm2 /rec k +⊗ (compose (nm / S +⊗ xs⁺) ys⁺)
  compose (nm / S +⊗ xs⁺) (give-K t ys⁺) = compose xs⁺ ys⁺ -- This can't be rightnmnm
  compose (nm /rec j +⊗ xs⁺) (rec k ⊗ ys⁺) = nm /rec (uninv ∘ k) +⊗ (compose xs⁺ ys⁺)
  compose (nm /rec j +⊗ xs⁺) (nm2 / T +⊗ ys⁺) = nm2 / T +⊗ (compose (nm /rec j +⊗ xs⁺) ys⁺)
  compose (nm /rec j +⊗ xs⁺) (nm2 /rec k +⊗ ys⁺) = nm2 /rec k +⊗ (compose (nm /rec j +⊗ xs⁺) ys⁺)
  compose {d = d} (give-K s xs⁺) ys⁺ = give-K (s ∘ apply d) (compose xs⁺ ys⁺)
  compose `0 `0 = `0
  compose (nmf ∣ x⁺ ⊕ xs⁺) (nmf2 ∣ y⁺ ⊕ ys⁺) = nmf2 ∘ nmf ∣ (compose x⁺ y⁺) ⊕ (compose xs⁺ ys⁺)

  -- To prove that composition is sound we show that the right description is
  -- returned. The descriptions contain higher order terms so we use
  -- extensionality to compare them.
  module _ (ext : ∀{a b} → Extensionality a b) where
    compose-sound : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
                    (o : Orn u c D) → (p : Orn v d (ornToDesc o)) →
                    (ornToDesc (compose o p)) ≡ ornToDesc p
    compose-sound {d = d} (ι j) (ι k) = cong ι (ext (λ x → uninv-inv-∘ (j (apply d x)) (k x)))
    compose-sound (ι {i = i} {c} j) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (compose-sound (ι {i = i} {c} j) ys⁺)
    compose-sound (ι {i = i} {c} j) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (compose-sound (ι {i = i} {c} j) ys⁺)
    compose-sound (-⊗ xs⁺) (-⊗ ys⁺) = cong (_/_⊗_ _ _) (compose-sound xs⁺ ys⁺)
    compose-sound (-⊗ xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (compose-sound (-⊗ xs⁺) ys⁺)
    compose-sound (-⊗ xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (compose-sound (-⊗ xs⁺) ys⁺)
    compose-sound (-⊗ xs⁺) (give-K t ys⁺) = compose-sound xs⁺ ys⁺
    compose-sound {d = d} (rec j ⊗ xs⁺) (rec k ⊗ ys⁺) =
      cong₂ (_/rec_⊗_ _) (ext (λ x → uninv-inv-∘ (j (apply d x)) (k x))) (compose-sound xs⁺ ys⁺)
    compose-sound (rec_⊗_ {i = i} j xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (compose-sound (rec_⊗_ {i = i} j xs⁺) ys⁺)
    compose-sound (rec_⊗_ {i = i} j xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (compose-sound (rec_⊗_ {i = i} j xs⁺) ys⁺)
    compose-sound {d = d} (nm / S +⊗ xs⁺) (-⊗ ys⁺) = cong (_/_⊗_ nm (S ∘ apply d)) (compose-sound xs⁺ ys⁺)
    compose-sound (nm / S +⊗ xs⁺) (nm2 / T +⊗ ys⁺) = cong (_/_⊗_ nm2 T) (compose-sound (nm / S +⊗ xs⁺) ys⁺)
    compose-sound (nm / S +⊗ xs⁺) (nm2 /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm2 k) (compose-sound (nm / S +⊗ xs⁺) ys⁺)
    compose-sound (nm / S +⊗ xs⁺) (give-K t ys⁺) = compose-sound xs⁺ ys⁺
    compose-sound (nm /rec j +⊗ xs⁺) (rec k ⊗ ys⁺) = cong (_/rec_⊗_ nm (uninv ∘ k)) (compose-sound xs⁺ ys⁺)
    compose-sound (nm /rec j +⊗ xs⁺) (nm2 / T +⊗ ys⁺) = cong (_/_⊗_ nm2 T) (compose-sound (nm /rec j +⊗ xs⁺) ys⁺)
    compose-sound (nm /rec j +⊗ xs⁺) (nm2 /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm2 k) (compose-sound (nm /rec j +⊗ xs⁺) ys⁺)
    compose-sound (give-K s xs⁺) ys⁺ = compose-sound xs⁺ ys⁺
    compose-sound `0 `0 = refl
    compose-sound (nmf ∣ x⁺ ⊕ xs⁺) (nmf2 ∣ y⁺ ⊕ ys⁺) = cong₂ (_∣_⊕_ _) (compose-sound x⁺ y⁺) (compose-sound xs⁺ ys⁺)


----------------------------------------
-- Reornaments currently only work when the original datatype does not have
-- parameters. To make it work for all datatypes, the indices have to be
-- dependent on the parameters. (See handwritten notes)

reornament : ∀{I J Δ}{u : J → I}{c : Cxf Δ ε}{#c}{D : DatDesc I ε #c} →
             (o : Orn u c D) → Orn (u ∘ fst) (cxf-∘ c (cxf-id Δ)) D
reornament o = compose o (algOrn (ornToDesc o) (λ {δ} → forgetAlg o {δ}))

