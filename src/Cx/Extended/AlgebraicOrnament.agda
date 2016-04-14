
module Cx.Extended.AlgebraicOrnament where

open import Common
open import Cx.Extended.Ornament public


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
  algOrn {dt = isCon} (S ⊗ xs) α = -⊗ (algOrn xs (λ {γ} → curry α (top γ)))
  algOrn {dt = isCon} {c = c} (rec i ⊗ xs) α = insert (J ∘ i ∘ apply c)
                                             ⊗ rec (λ δ → inv (i (apply c (pop δ)) , top δ))
                                             ⊗ algOrn xs (λ {δ} → curry α (top δ))
  algOrn {dt = isDat _} `0 α = `0
  algOrn {dt = isDat _} (x ⊕ xs) α = algOrn x (curry α 0) ⊕ algOrn xs (α ∘ (suc *** id))


----------------------------------------
-- Composition of ornaments

module _ {I J K : Set}{u : J → I}{v : K → J} where
  compose : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
            (o : Orn u c D) → Orn v d (ornToDesc o) → Orn (u ∘ v) (cxf-∘ c d) D
  compose (ι j) (ι k) = ι (λ _ → inv-∘ (j _) (k _))
  compose (ι j) (insert T ⊗ ys⁺) = insert T ⊗ (compose (ι j) ys⁺)
  compose (ι j) (insert-rec k ⊗ ys⁺) = insert-rec k ⊗ (compose (ι j) ys⁺)
  compose (-⊗ xs⁺) (-⊗ ys⁺) = -⊗ (compose xs⁺ ys⁺)
  compose (-⊗ xs⁺) (insert T ⊗ ys⁺) = insert T ⊗ (compose (-⊗ xs⁺) ys⁺)
  compose (-⊗ xs⁺) (insert-rec j ⊗ ys⁺) = insert-rec j ⊗ (compose (-⊗ xs⁺) ys⁺)
  compose (-⊗ xs⁺) (give-K t ys⁺) = give-K t (compose xs⁺ ys⁺)
  compose (rec j ⊗ xs⁺) (rec k ⊗ ys⁺) = rec (λ _ → inv-∘ (j _) (k _)) ⊗ compose xs⁺ ys⁺
  compose (rec j ⊗ xs⁺) (insert T ⊗ ys⁺) = insert T ⊗ (compose (rec j ⊗ xs⁺) ys⁺)
  compose (rec j ⊗ xs⁺) (insert-rec k ⊗ ys⁺) = insert-rec k ⊗ (compose (rec j ⊗ xs⁺) ys⁺)
  compose {d = d} (insert S ⊗ xs⁺) (-⊗ ys⁺) = insert (S ∘ apply d) ⊗ (compose xs⁺ ys⁺)
  compose (insert S ⊗ xs⁺) (insert T ⊗ ys⁺) = insert T ⊗ (compose (insert S ⊗ xs⁺) ys⁺)
  compose (insert S ⊗ xs⁺) (insert-rec k ⊗ ys⁺) = insert-rec k ⊗ (compose (insert S ⊗ xs⁺) ys⁺)
  compose (insert S ⊗ xs⁺) (give-K t ys⁺) = compose xs⁺ ys⁺ -- This can't be right??
  compose (insert-rec j ⊗ xs⁺) (rec k ⊗ ys⁺) = insert-rec (uninv ∘ k) ⊗ (compose xs⁺ ys⁺)
  compose (insert-rec j ⊗ xs⁺) (insert T ⊗ ys⁺) = insert T ⊗ (compose (insert-rec j ⊗ xs⁺) ys⁺)
  compose (insert-rec j ⊗ xs⁺) (insert-rec k ⊗ ys⁺) = insert-rec k ⊗ (compose (insert-rec j ⊗ xs⁺) ys⁺)
  compose {d = d} (give-K s xs⁺) ys⁺ = give-K (s ∘ apply d) (compose xs⁺ ys⁺)
  compose `0 `0 = `0
  compose (x⁺ ⊕ xs⁺) (y⁺ ⊕ ys⁺) = (compose x⁺ y⁺) ⊕ (compose xs⁺ ys⁺)

  -- To prove that composition is sound we show that the right description is
  -- returned. The descriptions contain higher order terms so we use
  -- extensionality to compare them.
  module _ (ext : ∀{a b} → Extensionality a b) where
    compose-sound : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
                    (o : Orn u c D) → (p : Orn v d (ornToDesc o)) →
                    (ornToDesc (compose o p)) ≡ ornToDesc p
    compose-sound {d = d} (ι j) (ι k) = cong ι (ext (λ x → uninv-inv-∘ (j (apply d x)) (k x)))
    compose-sound (ι {i = i} {c} j) (insert T ⊗ ys⁺) = cong (_⊗_ T) (compose-sound (ι {i = i} {c} j) ys⁺)
    compose-sound (ι {i = i} {c} j) (insert-rec k ⊗ ys⁺) = cong (rec_⊗_ k) (compose-sound (ι {i = i} {c} j) ys⁺)
    compose-sound (-⊗ xs⁺) (-⊗ ys⁺) = cong (_⊗_ _) (compose-sound xs⁺ ys⁺)
    compose-sound (-⊗ xs⁺) (insert T ⊗ ys⁺) = cong (_⊗_ T) (compose-sound (-⊗ xs⁺) ys⁺)
    compose-sound (-⊗ xs⁺) (insert-rec k ⊗ ys⁺) = cong (rec_⊗_ k) (compose-sound (-⊗ xs⁺) ys⁺)
    compose-sound (-⊗ xs⁺) (give-K t ys⁺) = compose-sound xs⁺ ys⁺
    compose-sound {d = d} (rec j ⊗ xs⁺) (rec k ⊗ ys⁺) =
      cong₂ rec_⊗_ (ext (λ x → uninv-inv-∘ (j (apply d x)) (k x))) (compose-sound xs⁺ ys⁺)
    compose-sound (rec_⊗_ {i = i} j xs⁺) (insert T ⊗ ys⁺) = cong (_⊗_ T) (compose-sound (rec_⊗_ {i = i} j xs⁺) ys⁺)
    compose-sound (rec_⊗_ {i = i} j xs⁺) (insert-rec k ⊗ ys⁺) = cong (rec_⊗_ k) (compose-sound (rec_⊗_ {i = i} j xs⁺) ys⁺)
    compose-sound {d = d} (insert S ⊗ xs⁺) (-⊗ ys⁺) = cong (_⊗_ (S ∘ apply d)) (compose-sound xs⁺ ys⁺)
    compose-sound (insert S ⊗ xs⁺) (insert T ⊗ ys⁺) = cong (_⊗_ T) (compose-sound (insert S ⊗ xs⁺) ys⁺)
    compose-sound (insert S ⊗ xs⁺) (insert-rec k ⊗ ys⁺) = cong (rec_⊗_ k) (compose-sound (insert S ⊗ xs⁺) ys⁺)
    compose-sound (insert S ⊗ xs⁺) (give-K t ys⁺) = compose-sound xs⁺ ys⁺
    compose-sound (insert-rec j ⊗ xs⁺) (rec k ⊗ ys⁺) = cong (rec_⊗_ (uninv ∘ k)) (compose-sound xs⁺ ys⁺)
    compose-sound (insert-rec j ⊗ xs⁺) (insert T ⊗ ys⁺) = cong (_⊗_ T) (compose-sound (insert-rec j ⊗ xs⁺) ys⁺)
    compose-sound (insert-rec j ⊗ xs⁺) (insert-rec k ⊗ ys⁺) = cong (rec_⊗_ k) (compose-sound (insert-rec j ⊗ xs⁺) ys⁺)
    compose-sound (give-K s xs⁺) ys⁺ = compose-sound xs⁺ ys⁺
    compose-sound `0 `0 = refl
    compose-sound (x⁺ ⊕ xs⁺) (y⁺ ⊕ ys⁺) = cong₂ _⊕_ (compose-sound x⁺ y⁺) (compose-sound xs⁺ ys⁺)


----------------------------------------
-- Reornaments currently only work when the original datatype does not have
-- parameters. To make it work for all datatypes, the indices have to be
-- dependent on the parameters. (See handwritten notes)
reornament : ∀{I J Δ}{u : J → I}{c : Cxf Δ ε}{#c}{D : DatDesc I ε #c} →
             (o : Orn u c D) → Orn (u ∘ fst) (cxf-∘ c (cxf-id Δ)) D
reornament o = compose o (algOrn (ornToDesc o) (λ {δ} → forgetAlg o {δ}))

