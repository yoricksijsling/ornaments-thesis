
module Cx.Cx where

open import Prelude
open import Common

infixl 0 _▶_

-- Exactly Σ, but looks better with the nesting produced by Cx.
record _▶_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pop : A
    top : B pop
open _▶_ public

infixl 0 _▷_ _▷₁_
mutual
  -- Terrible hack only works with two levels. The only levels which are sure to
  -- be contained in (lsuc a) for any a, are 0 and a.
  data Cx {a : Level} : Set (lsuc a) where
    _▷₁_ : {{p : a ≡ lsuc lzero}}(Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set a) → Cx {a}
    _▷_ : (Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set) → Cx {a}
    ε : Cx

  ⟦_⟧Cx : ∀{a} → Cx {a} → Set a
  ⟦ Γ ▷₁ S ⟧Cx = (⟦ Γ ⟧Cx ▶ S)
  ⟦ Γ ▷ S ⟧Cx = (⟦ Γ ⟧Cx ▶ S)
  ⟦ ε ⟧Cx = ⊤′

infixl 0 _▷′_ _▷₁′_
_▷′_ : ∀{a}(Γ : Cx {a}) → Set → Cx {a}
Γ ▷′ S = Γ ▷ const S
_▷₁′_ : (Γ : Cx) → Set₁ → Cx
Γ ▷₁′ S = Γ ▷₁ const S


instance Cx-semantics : ∀{a} → Semantics (Cx {a})
         Cx-semantics = record { ⟦_⟧ = ⟦_⟧Cx }
{-# DISPLAY ⟦_⟧Cx x = ⟦_⟧ x #-}

Cx₀ : Set₁
Cx₀ = Cx {lzero}
Cx₁ : Set₂
Cx₁ = Cx {lsuc lzero}


-- Wrap this function in a record to help the type checker
-- Alternatively, the values in Cx could be indexed by the original Cx?
record Cxf {a}(Γ Δ : Cx {a}) : Set (lsuc a) where
  constructor mk
  field
    apply : ⟦ Γ ⟧ → ⟦ Δ ⟧

infixr 0 _$$_
_$$_ : ∀{a}{Γ Δ : Cx {a}} → Cxf Γ Δ → ⟦ Γ ⟧ → ⟦ Δ ⟧
f $$ x = Cxf.apply f x

cxf-make : ∀{a}(Γ Δ : Cx {a}) → (⟦ Γ ⟧ → ⟦ Δ ⟧) → Cxf Γ Δ
cxf-make _ _ = mk

cxf-id : ∀{a}(Γ : Cx {a}) → Cxf Γ Γ
cxf-id Γ = mk id

cxf-∘ : ∀{a}{Γ Δ Χ : Cx {a}} → (f : Cxf Δ Χ) → (g : Cxf Γ Δ) → Cxf Γ Χ
cxf-∘ f g = mk (_$$_ f ∘ _$$_ g)

cxf-both : ∀{a}{Γ Δ : Cx {a}}{S} → (f : Cxf Δ Γ) → Cxf (Δ ▷ (S ∘ _$$_ f)) (Γ ▷ S)
cxf-both f = mk λ δ → (f $$ pop δ) , top δ

cxf-forget : ∀{a}{Γ Δ : Cx {a}} → (f : Cxf Δ Γ) → (S : ⟦ Δ ⟧ → Set) → Cxf (Δ ▷ S) Γ
cxf-forget f S = mk λ δ → f $$ pop δ

cxf-instantiate : ∀{a}{Γ Δ : Cx {a}}{S} → (f : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → S (f $$ γ)) → Cxf Δ (Γ ▷ S)
cxf-instantiate f s = mk λ δ → (f $$ δ) , s δ

cxf-instantiateSet : ∀{Γ Δ : Cx₁}{S} → (f : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → S (f $$ γ)) → Cxf Δ (Γ ▷₁ S)
cxf-instantiateSet f s = mk λ δ → (f $$ δ) , s δ

cxf-Inv : ∀{a}{Γ Δ : Cx {a}} → Cxf Δ Γ → ⟦ Γ ⟧ → Set _
cxf-Inv f γ = _$$_ f ⁻¹ γ
