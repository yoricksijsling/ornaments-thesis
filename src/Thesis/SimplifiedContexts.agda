
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

example-Γ : Cx
example-Γ = ε ▷′ Set ▷′ Nat ▷ (λ γ → Vec (top (pop γ)) (top γ))

example-γ : ⟦ example-Γ ⟧Cx
example-γ = ((tt , String) , 3) , "test" ∷ "1" ∷ "2" ∷ []


Cxf : (Γ Δ : Cx) → Set
Cxf Γ Δ = ⟦ Γ ⟧ → ⟦ Δ ⟧

cxf-both : ∀{Γ Δ S} → (f : Cxf Δ Γ) → Cxf (Δ ▷ (S ∘ f)) (Γ ▷ S)
cxf-both f δ = f (pop δ) , top δ

cxf-forget : ∀{Γ Δ} → (f : Cxf Δ Γ) → (S : ⟦ Δ ⟧ → Set) → Cxf (Δ ▷ S) Γ
cxf-forget f S δ = f (pop δ)

cxf-instantiate : ∀{Γ Δ S} → (f : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → S (f γ)) → Cxf Δ (Γ ▷ S)
cxf-instantiate f s δ = f δ , s δ
