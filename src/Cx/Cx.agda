
module Cx.Cx where

open import Prelude
open import Common

infixl 0 _▷_ _▷Set _▶_

-- Exactly Σ, but looks better with the nesting produced by Cx.
record _▶_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pop : A
    top : B pop
open _▶_ public

mutual
  data Cx : Set₂ where
    _▷Set : (Γ : Cx) → Cx
    _▷_ : (Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set) → Cx
    ε : Cx

  ⟦_⟧Cx : Cx → Set₁
  ⟦ Γ ▷Set ⟧Cx = (⟦ Γ ⟧Cx ▶ const Set)
  ⟦ Γ ▷ S ⟧Cx = (⟦ Γ ⟧Cx ▶ S)
  ⟦ ε ⟧Cx = ⊤′

instance Cx-semantics : Semantics Cx
         Cx-semantics = record { ⟦_⟧ = ⟦_⟧Cx }
{-# DISPLAY ⟦_⟧Cx x = ⟦_⟧ x #-}



-- Wrap this function in a record to help the type checker
record Cxf (Γ Δ : Cx) : Set₁ where
  constructor mk
  field
    apply : ⟦ Γ ⟧ → ⟦ Δ ⟧
-- Circumventing a bug which occurs in Cx.Named.Ornament. Something with passing
-- parameters to modules in combination with records and datatypes...
apply : {Γ Δ : Cx} → Cxf Γ Δ → ⟦ Γ ⟧ → ⟦ Δ ⟧
apply = Cxf.apply

cxf-make : ∀ Γ Δ → (⟦ Γ ⟧ → ⟦ Δ ⟧) → Cxf Γ Δ
cxf-make _ _ = mk

cxf-id : ∀ Γ → Cxf Γ Γ
cxf-id Γ = mk id

cxf-∘ : ∀{Γ Δ Χ} → (f : Cxf Δ Χ) → (g : Cxf Γ Δ) → Cxf Γ Χ
cxf-∘ f g = mk (apply f ∘ apply g)

cxf-both : ∀{Γ Δ S} → (f : Cxf Δ Γ) → Cxf (Δ ▷ (S ∘ apply f)) (Γ ▷ S)
cxf-both f = mk λ δ → apply f (pop δ) , top δ

cxf-forget : {Γ Δ : Cx} → (f : Cxf Δ Γ) → (S : ⟦ Δ ⟧ → Set) → Cxf (Δ ▷ S) Γ
cxf-forget f S = mk λ δ → apply f (pop δ)

cxf-instantiate : ∀{Γ Δ S} → (f : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → S (apply f γ)) → Cxf Δ (Γ ▷ S)
cxf-instantiate f s = mk λ δ → (apply f δ) , s δ

cxf-instantiateSet : ∀{Γ Δ} → (f : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → Set) → Cxf Δ (Γ ▷Set)
cxf-instantiateSet f s = mk λ δ → (apply f δ) , s δ
