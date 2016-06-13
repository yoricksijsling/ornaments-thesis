
module Cx.Extended.Desc where

open import Common
open import Cx.Cx public

infixr 2 _⊕_
infixr 3 _⊗_ rec_⊗_
data ConDesc (I : Cx₀)(Γ : Cx₁) : Set₁ where
  ι : (o : (γ : ⟦ Γ ⟧) → ⟦ I ⟧) → ConDesc I Γ
  _⊗_ : (S : (γ : ⟦ Γ ⟧) → Set) → (xs : ConDesc I (Γ ▷ S)) → ConDesc I Γ
  rec_⊗_ : (i : (γ : ⟦ Γ ⟧) → ⟦ I ⟧) → (xs : ConDesc I Γ) → ConDesc I Γ
data DatDesc (I : Cx)(Γ : Cx) : (#c : Nat) → Set₁ where
  `0 : DatDesc I Γ 0
  _⊕_ : ∀{#c}(x : ConDesc I Γ)(xs : DatDesc I Γ #c) →
    DatDesc I Γ (suc #c)


----------------------------------------
-- Semantics

data DescTag : Set₂ where
  isCon : DescTag
  isDat : (#c : Nat) → DescTag

Desc : (I : Cx) → (Γ : Cx) → DescTag → Set₁
Desc I Γ (isCon) = ConDesc I Γ
Desc I Γ (isDat #c) = DatDesc I Γ #c

lookupCtor : ∀{I Γ #c}(D : DatDesc I Γ #c) → Fin #c → ConDesc I Γ
lookupCtor `0 ()
lookupCtor (x ⊕ _) zero = x
lookupCtor (_ ⊕ xs) (suc k) = lookupCtor xs k

private
  ⟦_⟧conDesc : ∀{I Γ} → ConDesc I Γ → ⟦ Γ ⟧ → (⟦ I ⟧ → Set) → (⟦ I ⟧ → Set)
  ⟦ ι o ⟧conDesc γ X o′ = o γ ≡ o′
  ⟦ S ⊗ xs ⟧conDesc γ X o = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X o
  ⟦ rec i ⊗ xs ⟧conDesc γ X o = X (i γ) × ⟦ xs ⟧conDesc γ X o
⟦_⟧desc : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → (⟦ I ⟧ → Set) → (⟦ I ⟧ → Set)
⟦_⟧desc {dt = isCon} = ⟦_⟧conDesc
⟦_⟧desc {dt = isDat #c} D γ X o = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc γ X o

instance desc-semantics : ∀{I Γ dt} → Semantics (Desc I Γ dt)
         desc-semantics = record { ⟦_⟧ = ⟦_⟧desc }
{-# DISPLAY ⟦_⟧conDesc x = ⟦_⟧ x #-}
{-# DISPLAY ⟦_⟧desc x = ⟦_⟧ x #-}

data μ {I Γ #c} (D : DatDesc I Γ #c) (γ : ⟦ Γ ⟧) (o : ⟦ I ⟧) : Set where
  ⟨_⟩ : ⟦ D ⟧ γ (μ D γ) o → μ D γ o


----------------------------------------
-- Map

descmap : ∀{I Γ dt X Y} (f : X →ⁱ Y) (D : Desc I Γ dt) →
  ∀{γ} → ⟦ D ⟧ γ X →ⁱ ⟦ D ⟧ γ Y
descmap {dt = isCon} f (ι o) p = p
descmap {dt = isCon} f (S ⊗ xs) (s , v) = s , descmap f xs v
descmap {dt = isCon} f (rec i ⊗ xs) (s , v) = f s , descmap f xs v
descmap {dt = isDat _} f xs (k , v) = k , descmap f (lookupCtor xs k) v


----------------------------------------
-- Folding

-- Passing the context makes sense, because an algebra may be specific to a
-- particular context. If the algebra is for a whole datatype, the context
-- corresponds with the parameters. 
-- sumAlg : Alg listD (ε ▶ Nat) (const Nat)
-- lengthAlg : ∀{A} → Alg listD (ε ▶ A) (const Nat)

Alg : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → (⟦ I ⟧ → Set) → Set
Alg {I} D γ X = ⟦ D ⟧ γ X →ⁱ X

module Fold {I Γ #c}{D : DatDesc I Γ #c}{γ X} (α : Alg D γ X) where
  mutual
    fold : μ D γ →ⁱ X
    fold ⟨ xs ⟩ = α (descmap-fold D xs)

    -- The normal descmap specialised to fold. Needed for termination checking
    descmap-fold : ∀{dt Γ′} (D′ : Desc I Γ′ dt) {γ′} → ⟦ D′ ⟧ γ′ (μ D γ) →ⁱ ⟦ D′ ⟧ γ′ X
    descmap-fold {isCon} (ι o) refl = refl
    descmap-fold {isCon} (S ⊗ xs) (s , v) = s , descmap-fold xs v
    descmap-fold {isCon} (rec i′ ⊗ xs) (s , v) = fold s , descmap-fold xs v
    descmap-fold {isDat _} xs (k , v) = k , descmap-fold (lookupCtor xs k) v
open Fold using (fold) public
