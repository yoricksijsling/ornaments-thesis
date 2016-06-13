
module Cx.Cx.Core where

open import Prelude
open import Common

infixl 0 _▶₁_ _▶₀_
record _▶₁_ (A : Set₁) (B : A → Set₁) : Set₁ where
  constructor _,_
  field
    pop₁ : A
    top₁ : B pop₁
open _▶₁_ public

record _▶₀_ {a} (A : Set a) (B : A → Set) : Set a where
  constructor _,_
  field
    pop₀ : A
    top₀ : B pop₀
open _▶₀_ public

record Popable {a b} (_▶_ : (A : Set a) (B : A → Set b) → Set (a ⊔ b)) : Set (lsuc (a ⊔ b)) where
  field
    pop : {A : Set a} {B : A → Set b} → A ▶ B → A
    top : {A : Set a} {B : A → Set b} → (v : A ▶ B) → B (pop v)
    _,ᵖ_ : {A : Set a} {B : A → Set b} → (x : A) → (y : B x) → A ▶ B
open Popable {{...}} public

instance
  Popable-▶₁ : Popable _▶₁_
  Popable-▶₁ = record { pop = pop₁ ; top = top₁ ; _,ᵖ_ = _,_ }
  Popable-▶₀ : ∀{a} → Popable {a} _▶₀_
  Popable-▶₀ = record { pop = pop₀ ; top = top₀ ; _,ᵖ_ = _,_ }
{-# DISPLAY pop₁ = pop #-}
{-# DISPLAY top₁ = top #-}
{-# DISPLAY pop₀ = pop #-}
{-# DISPLAY top₀ = top #-}


----------------------------------------

infixl 0 _▷_ _▷₁_
mutual
  -- Terrible hack, still only works with two levels. The only levels
  -- which are sure to be contained in (lsuc a) for any a, are 0 and
  -- a.
  data Cx {a : Level} : Set (lsuc a) where
    _▷₁_ : {{p : a ≡ lsuc lzero}}(Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set a) → Cx {a}
    _▷_ : (Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set) → Cx {a}
    ε : Cx

  ⟦_⟧Cx : ∀{a} → Cx {a} → Set a
  ⟦ _▷₁_ {{refl}} Γ S ⟧Cx = ⟦ Γ ⟧Cx ▶₁ S
  ⟦ _▷_ Γ S ⟧Cx = ⟦ Γ ⟧Cx ▶₀ S
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

Cxf : ∀{a}(Γ Δ : Cx {a}) → Set a
Cxf Γ Δ = ⟦ Γ ⟧ → ⟦ Δ ⟧

cxf-both : ∀{a}{Γ Δ : Cx {a}}{S} → (c : Cxf Δ Γ) → Cxf (Δ ▷ (S ∘ c)) (Γ ▷ S)
cxf-both f δ = (f $ pop δ) , top δ

cxf-forget : ∀{a}{Γ Δ : Cx {a}} → (c : Cxf Δ Γ) → (S : ⟦ Δ ⟧ → Set) → Cxf (Δ ▷ S) Γ
cxf-forget f S δ = f (pop δ)

cxf-inst : ∀{a}{Γ Δ : Cx {a}}{S} → (c : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → S (c γ)) → Cxf Δ (Γ ▷ S)
cxf-inst f s δ = f δ , s δ

-- cxf-instSet : ∀{Γ Δ : Cx₁}{S} → (c : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → S (c γ)) → Cxf Δ (Γ ▷₁ S)
-- cxf-instSet f s δ = f δ , s δ


Cx-walk : {A B : Set} → A → (d₁ : A → A) → (d₀ : A → A) →
        (fε : A → B) → (u₁ : A → B → B) → (u₀ : A → B → B) →
        ∀{ℓ} → Cx {ℓ} → B
Cx-walk {A} {B} a d₁ d₀ fε u₁ u₀ = helper a
  where
  helper : A → Cx → B
  helper a (Γ ▷₁ S) = u₁ a (helper (d₁ a) Γ)
  helper a (Γ ▷ S) = u₀ a (helper (d₀ a) Γ)
  helper a ε = fε a

Cx-iter : {B : Set} → (f : B → B) → (x : B) → ∀{a} → Cx {a} → B
Cx-iter {B} f x = Cx-walk {⊤} {B} tt id id (const x) (const f) (const f)

CxLength : ∀{ℓ} → Cx {ℓ} → Nat
CxLength = Cx-iter {Nat} suc 0

