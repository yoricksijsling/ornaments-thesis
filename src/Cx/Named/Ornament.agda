
module Cx.Named.Ornament where

open import Common
open import Cx.Named.Desc public

infixr 3 _⊕_
infixr 4 _/-⊗_ _/rec_⊗_ _/_+⊗_ _/rec_+⊗_
-- The `u` function tells us how the ornament changes the indices of the current Desc.
-- The `c` function specifies how the context outside the current Desc has changed.
data Orn {I J : Set}(u : J → I) : ∀{Γ Δ dt} (c : Cxf Δ Γ) (D : Desc I Γ dt) → Set₁ where
  ι : ∀{Γ Δ i}{c : Cxf Δ Γ} → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (apply c δ))) → Orn u c (ι i)
  _/-⊗_ : ∀{Γ Δ nm S xs}{c : Cxf Δ Γ} → (nm′ : String) →
          (xs⁺ : Orn u (cxf-both c) xs) → Orn u c (nm / S ⊗ xs)
  _/rec_⊗_ : ∀{Γ Δ nm i xs}{c : Cxf Δ Γ} → (nm′ : String) →
             (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (apply c δ))) → (xs⁺ : Orn u c xs) → Orn u c (nm /rec i ⊗ xs)

  _/_+⊗_ : ∀{Γ Δ}{c : Cxf Δ Γ}{xs : ConDesc I Γ} →
            (nm : String) (S : (δ : ⟦ Δ ⟧) → Set) (xs⁺ : Orn u (cxf-forget c S) xs) → Orn u c xs
  _/rec_+⊗_ : ∀{Γ Δ}{c : Cxf Δ Γ}{xs : ConDesc I Γ} →
               (nm : String) (j : (δ : ⟦ Δ ⟧) → J) (xs⁺ : Orn u c xs) → Orn u c xs
  give-K : ∀{Γ Δ S xs nm}{c : Cxf Δ Γ} →
           (s : (δ : ⟦ Δ ⟧) → S (apply c δ)) →
           (xs⁺ : Orn u (cxf-instantiate c s) xs) →
           Orn u c (nm / S ⊗ xs)

  `0 : ∀{Γ Δ}{c : Cxf Δ Γ} → Orn u c `0
  _⊕_ : ∀{Γ Δ #c x}{c : Cxf Δ Γ}{xs : DatDesc I Γ #c}
         (x⁺ : Orn u c x) (xs⁺ : Orn u c xs) → Orn u c (x ⊕ xs)

DefOrn : ∀{I}(J : Set)(u : J → I) {Γ}(Δ : Cx)(c : Cxf Δ Γ) {dt}(D : Desc I Γ dt) → Set₁
DefOrn J u Δ c D = Orn u c D


----------------------------------------
-- Semantics

module _ {I J : Set}{u : J → I} where
  ornToDesc : ∀{Γ Δ dt}{c : Cxf Δ Γ}{D : Desc I Γ dt} → (o : Orn u c D) → Desc J Δ dt
  ornToDesc {c = c} (ι j) = ι (uninv ∘ j)
  ornToDesc (_/-⊗_ {S = S} {c = c} nm xs⁺) = nm / S ∘ apply c ⊗ ornToDesc xs⁺
  ornToDesc (_/rec_⊗_ nm j xs⁺) = nm /rec (uninv ∘ j) ⊗ ornToDesc xs⁺
  ornToDesc (_/_+⊗_ nm S xs⁺) = nm / S ⊗ ornToDesc xs⁺
  ornToDesc (_/rec_+⊗_ nm j xs⁺) = nm /rec j ⊗ ornToDesc xs⁺
  ornToDesc (give-K s xs⁺) = ornToDesc xs⁺
  ornToDesc `0 = `0
  ornToDesc (_⊕_ x⁺ xs⁺) = ornToDesc x⁺ ⊕ ornToDesc xs⁺

  instance orn-semantics : ∀{Γ Δ dt}{c : Cxf Δ Γ}{D : Desc I Γ dt} → Semantics (Orn u c D)
           orn-semantics = record { ⟦_⟧ = ⟦_⟧ ∘ ornToDesc }


----------------------------------------
-- Identity ornament

idOrn : ∀{I Γ dt}{D : Desc I Γ dt} → Orn id (cxf-id Γ) D
idOrn {dt = isCon} {ι o} = ι (λ δ → inv (o δ))
idOrn {dt = isCon} {nm / S ⊗ xs} = nm /-⊗ idOrn
idOrn {dt = isCon} {nm /rec i ⊗ xs} = nm /rec (λ δ → inv (i δ)) ⊗ idOrn
idOrn {dt = isDat _} {`0} = `0
idOrn {dt = isDat _} {x ⊕ xs} = idOrn ⊕ idOrn

idOrn-sound : ∀{I Γ dt} → (D : Desc I Γ dt) → ornToDesc (idOrn {D = D}) ≡ D
idOrn-sound {dt = isCon} (ι o) = refl
idOrn-sound {dt = isCon} (nm / S ⊗ xs) = cong (_/_⊗_ nm S) (idOrn-sound xs)
idOrn-sound {dt = isCon} (nm /rec i ⊗ xs) = cong (_/rec_⊗_ nm i) (idOrn-sound xs)
idOrn-sound {dt = isDat .0} `0 = refl
idOrn-sound {dt = isDat _} (x ⊕ xs) = cong₂ _⊕_ (idOrn-sound x) (idOrn-sound xs)


----------------------------------------
-- Ornamental algebra

module _ {I J : Set}{u : J → I} where
  forgetNT : ∀{Γ Δ dt}{c : Cxf Δ Γ}{D : Desc I Γ dt} (o : Orn u c D) →
             ∀ {δ X j} → ⟦ o ⟧ δ (X ∘ u) j → ⟦ D ⟧ (apply c δ) X (u j)
  forgetNT {c = c} (ι j) {δ} refl = sym (inv-eq (j δ))
  forgetNT (_/-⊗_ _ xs⁺) (s , v) = s , forgetNT xs⁺ v
  forgetNT (_/rec_⊗_ _ j xs⁺) {δ} {X} (s , v) = transport X (inv-eq (j δ)) s , forgetNT xs⁺ v
  forgetNT (_/_+⊗_ _ _ xs⁺) (_ , v) = forgetNT xs⁺ v
  forgetNT (_/rec_+⊗_ _ _ xs⁺) (_ , v) = forgetNT xs⁺ v
  forgetNT (give-K s xs⁺) {δ} v = s δ , forgetNT xs⁺ v
  forgetNT `0 (() , _)
  forgetNT (x⁺ ⊕ xs⁺) (zero , v) = zero , forgetNT x⁺ v
  forgetNT (x⁺ ⊕ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

  forgetAlg : ∀{Γ Δ #c}{c : Cxf Δ Γ}{D : DatDesc I Γ #c} (o : Orn u c D) →
              ∀{δ} → Alg (ornToDesc o) δ (μ D (apply c δ) ∘ u)
  forgetAlg o = ⟨_⟩ ∘ forgetNT o

  forget : ∀{Γ Δ #c}{c : Cxf Δ Γ}{D : DatDesc I Γ #c} (o : Orn u c D) →
           ∀{δ j} → μ (ornToDesc o) δ j → μ D (apply c δ) (u j)
  forget o = fold (forgetAlg o)
  
