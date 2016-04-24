
module Cx.Cx where

open import Prelude
open import Common

infixl 0 _▶₁_ _▶₀_
record _▶₁_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pop : A
    top : B pop
record _▶₀_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pop : A
    top : B pop

record Popable {a b} (_▶_ : (A : Set a) (B : A → Set b) → Set (a ⊔ b)) : Set (lsuc (a ⊔ b)) where
  field
    pop : {A : Set a} {B : A → Set b} → A ▶ B → A
    top : {A : Set a} {B : A → Set b} → (v : A ▶ B) → B (pop v)
open Popable {{...}} public

instance
  Popable₁ : ∀{a b} → Popable {a} {b} _▶₁_
  Popable₁ = record { pop = _▶₁_.pop ; top = _▶₁_.top }
  Popable₀ : ∀{a b} → Popable {a} {b} _▶₀_
  Popable₀ = record { pop = _▶₀_.pop ; top = _▶₀_.top }
{-# DISPLAY _▶₁_.pop = pop #-}
{-# DISPLAY _▶₁_.top = top #-}
{-# DISPLAY _▶₀_.pop = pop #-}
{-# DISPLAY _▶₀_.top = top #-}


infixl 0 _▷_ _▷₁_
mutual
  -- Terrible hack only works with two levels. The only levels which are sure to
  -- be contained in (lsuc a) for any a, are 0 and a.
  data Cx {a : Level} : Set (lsuc a) where
    _▷₁_ : {{p : a ≡ lsuc lzero}}(Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set a) → Cx {a}
    _▷_ : (Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set) → Cx {a}
    ε : Cx

  ⟦_⟧Cx : ∀{a} → Cx {a} → Set a
  ⟦ Γ ▷₁ S ⟧Cx = ⟦ Γ ⟧Cx ▶₁ S
  ⟦ Γ ▷ S ⟧Cx = ⟦ Γ ⟧Cx ▶₀ S
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

cxf-both : ∀{a}{Γ Δ : Cx {a}}{S} → (f : Cxf Δ Γ) → Cxf (Δ ▷ (S ∘ f)) (Γ ▷ S)
cxf-both f δ = (f $ pop δ) , top δ

cxf-forget : ∀{a}{Γ Δ : Cx {a}} → (f : Cxf Δ Γ) → (S : ⟦ Δ ⟧ → Set) → Cxf (Δ ▷ S) Γ
cxf-forget f S δ = f (pop δ)

cxf-instantiate : ∀{a}{Γ Δ : Cx {a}}{S} → (f : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → S (f γ)) → Cxf Δ (Γ ▷ S)
cxf-instantiate f s δ = f δ , s δ

cxf-instantiateSet : ∀{Γ Δ : Cx₁}{S} → (f : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → S (f γ)) → Cxf Δ (Γ ▷₁ S)
cxf-instantiateSet f s δ = f δ , s δ


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
