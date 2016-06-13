
{-# OPTIONS --type-in-type #-}

module Thesis.SeparateContexts where

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

--------------------

module SemTest where
  Sem : (P : Cx) → (I Γ : (p : ⟦ P ⟧) → Cx) → Set
  Sem P I Γ = (p : ⟦ P ⟧) → (γ : ⟦ Γ p ⟧) → (X : ⟦ I p ⟧ → Set) → ((o : ⟦ I p ⟧) → Set)

  -- data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  --   instance refl : x ≡ x
  EqSem : Sem (ε ▷′ Set ▷ top) (λ p → ε ▷′ top (pop p)) (λ p → ε)
  EqSem p γ X o = (tt , top p) ≡ o

--------------------

module _ (P : Cx) (I : (p : ⟦ P ⟧) → Cx) where
  infixr 2 _⊕_
  infixr 3 _⊗_ rec_⊗_
  data ConDesc (Γ : (p : ⟦ P ⟧) → Cx) : Set where
    ι : (o : (p : ⟦ P ⟧)(γ : ⟦ Γ p ⟧) → ⟦ I p ⟧) → ConDesc Γ
    _⊗_ : (S : (p : ⟦ P ⟧)(γ : ⟦ Γ p ⟧) → Set) →
      (xs : ConDesc (λ p → Γ p ▷ S p)) → ConDesc Γ
    rec_⊗_ : (i : (p : ⟦ P ⟧)(γ : ⟦ Γ p ⟧) → ⟦ I p ⟧) →
      (xs : ConDesc Γ) → ConDesc Γ
  data DatDesc : (#c : Nat) → Set where
    `0 : DatDesc 0
    _⊕_ : ∀{#c} (x : ConDesc (const ε)) →
      (xs : DatDesc #c) → DatDesc (suc #c)

lookupCtor : ∀{P I #c}(D : DatDesc P I #c) → Fin #c → ConDesc P I (const ε)
lookupCtor `0 ()
lookupCtor (x ⊕ _) zero = x
lookupCtor (_ ⊕ xs) (suc k) = lookupCtor xs k

⟦_⟧conDesc : ∀{P I Γ} → ConDesc P I Γ →
  (p : ⟦ P ⟧) → (γ : ⟦ Γ p ⟧) → (X : ⟦ I p ⟧ → Set) → ((o : ⟦ I p ⟧) → Set)
⟦ ι o ⟧conDesc p γ X o′ = o p γ ≡ o′
⟦ S ⊗ xs ⟧conDesc p γ X o = Σ (S p γ) λ s → ⟦ xs ⟧conDesc p (γ , s) X o
⟦ rec i ⊗ xs ⟧conDesc p γ X o = X (i p γ) × ⟦ xs ⟧conDesc p γ X o
⟦_⟧datDesc : ∀{P I #c} → DatDesc P I #c →
  (p : ⟦ P ⟧) → (X : ⟦ I p ⟧ → Set) → ((o : ⟦ I p ⟧) → Set)
⟦_⟧datDesc D p X o = Σ (Fin _) λ k → ⟦ lookupCtor D k ⟧conDesc p tt X o

instance ConDesc-semantics : ∀{P I Γ} → Semantics (ConDesc P I Γ)
         ConDesc-semantics = record { ⟦_⟧ = ⟦_⟧conDesc }
         DatDesc-semantics : ∀{P I #c} → Semantics (DatDesc P I #c)
         DatDesc-semantics = record { ⟦_⟧ = ⟦_⟧datDesc }
{-# DISPLAY ⟦_⟧conDesc x = ⟦_⟧ x #-}
{-# DISPLAY ⟦_⟧datDesc x = ⟦_⟧ x #-}

data μ {P I #c} (D : DatDesc P I #c) (p : ⟦ P ⟧) (o : ⟦ I p ⟧) : Set where
  ⟨_⟩ : ⟦ D ⟧ p (μ D p) o → μ D p o

--------------------

data Silly (n : Nat) : Fin n → Set where
  silly : (k : Fin n) → (b : Bool) → Silly n k

SillyDesc : DatDesc (ε ▷′ Nat) (λ p → ε ▷′ Fin (top p)) 1
SillyDesc = (λ p γ → Fin (top p)) ⊗ (λ p γ → Bool)
  ⊗ ι (λ p γ → tt , top (pop γ)) ⊕ `0
silly-test : μ SillyDesc (tt , 10) (tt , 3)
silly-test = ⟨ 0 , 3 , true , refl ⟩

--------------------

data MyEq {A : Set} (x : A) : A → Set where
  refl : MyEq x x

EqDesc : DatDesc (ε ▷′ Set ▷ top) (λ p → ε ▷′ top (pop p)) 1
EqDesc = ι (λ p γ → tt , top p) ⊕ `0

to-eq : ∀{A x y} → MyEq x y → μ EqDesc ((tt , A) , x) (tt , y)
to-eq refl = ⟨ 0 , refl ⟩
from-eq : ∀{A x y} → μ EqDesc ((tt , A) , x) (tt , y) → MyEq x y
from-eq ⟨ zero , refl ⟩ = refl
from-eq ⟨ suc () , _ ⟩
