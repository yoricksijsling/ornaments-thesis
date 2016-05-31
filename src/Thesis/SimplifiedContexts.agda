
{-# OPTIONS --type-in-type #-}

module Thesis.SimplifiedContexts where

open import Common

infixl 0 _▶_
record _▶_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pop : A
    top : B pop
open _▶_

infixl 0 _▷_
mutual
  data Cx : Set₁ where
    _▷_ : (Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set) → Cx
    ε : Cx

  ⟦_⟧Cx : Cx → Set
  ⟦ Γ ▷ S ⟧Cx = ⟦ Γ ⟧Cx ▶ S
  ⟦ ε ⟧Cx = ⊤′

instance Cx-semantics : Semantics Cx
         Cx-semantics = record { ⟦_⟧ = ⟦_⟧Cx }

infixl 0 _▷′_
_▷′_ : (Γ : Cx) → Set → Cx
Γ ▷′ S = Γ ▷ const S

Cxf : (Γ Δ : Cx) → Set
Cxf Γ Δ = ⟦ Γ ⟧ → ⟦ Δ ⟧

cxf-both : ∀{Γ Δ S} → (c : Cxf Δ Γ) → Cxf (Δ ▷ (S ∘ c)) (Γ ▷ S)
cxf-both c δ = c (pop δ) , top δ

cxf-forget : ∀{Γ Δ} → (c : Cxf Δ Γ) → (S : ⟦ Δ ⟧ → Set) → Cxf (Δ ▷ S) Γ
cxf-forget c S δ = c (pop δ)

cxf-inst : ∀{Γ Δ S} → (c : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → S (c γ)) → Cxf Δ (Γ ▷ S)
cxf-inst c s δ = c δ , s δ
