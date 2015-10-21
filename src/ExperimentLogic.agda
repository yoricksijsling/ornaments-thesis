module ExperimentLogic where

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality

Pred : Set → Set₁
Pred I = I → Set

_⇒_ : ∀{I : Set} → (P Q : Pred I) → Set
P ⇒ Q = ∀{i} → P i → Q i

-- ⇒-trans : ∀{I} {P Q R : Pred I} (i : I) → (P i → Q i) → (Q i → R i) → (P i → R i)
-- ⇒-trans i PQ QR = QR ∘′ PQ

⇒-trans : ∀{I} {P Q R : Pred I} → P ⇒ Q → Q ⇒ R → P ⇒ R
-- ⇒-trans PQ QR {i} p = QR {i} (PQ {i} p)
⇒-trans PQ QR {i} = QR {i} ∘′ PQ {i} 

-- _⇒-∘_ : {P Q R : Set} → (Q → R) → (P → Q) → P → R
-- _⇒-∘_ QR PQ = QR ∘′ PQ

_⇒-∘_ : {I : Set}{P Q R : Pred I}{i : I} → (Q i → R i) → (P i → Q i) → P i → R i
_⇒-∘_ QR PQ = QR ∘′ PQ

module Even where
  data Even : Pred ℕ where
    evenZ : Even 0
    evenS : ∀{n} → Even n → Even (suc (suc n))
  
  Even' : Pred ℕ
  Even' zero = ⊤
  Even' (suc zero) = ⊥
  Even' (suc (suc n)) = Even' n
  
  Even⇒Even' : Even ⇒ Even'
  Even⇒Even' evenZ = tt
  Even⇒Even' (evenS P) = Even⇒Even' P
  
  Even'⇒Even : Even' ⇒ Even
  Even'⇒Even {zero} tt = evenZ
  Even'⇒Even {suc zero} ()
  Even'⇒Even {suc (suc i)} x = evenS (Even'⇒Even x)

  Even-id : ∀ {n} (P : Even n) → (Even'⇒Even ∘′ Even⇒Even') P ≡ P
  Even-id evenZ = refl
  Even-id (evenS E) = cong evenS (Even-id E)

  Even'-id : ∀{n} (P : Even' n) → (Even⇒Even' {n} ∘′ Even'⇒Even) P ≡ P
  Even'-id {zero} tt = refl
  Even'-id {suc zero} ()
  Even'-id {suc (suc n)} P = Even'-id {n} P

module Fin where
  data Fin : Pred ℕ where
    zero : {n : ℕ} → Fin (suc n)
    suc : {n : ℕ} (i : Fin n) → Fin (suc n)
  
  open import Data.Sum
  
  Fin' : Pred ℕ
  Fin' zero = ⊥
  Fin' (suc n) = ⊤ ⊎ (Fin' n)

  Fin⇒Fin' : Fin ⇒ Fin'
  Fin⇒Fin' zero = inj₁ tt
  Fin⇒Fin' (suc k) = inj₂ (Fin⇒Fin' k)

  Fin'⇒Fin : Fin' ⇒ Fin
  Fin'⇒Fin {zero} ()
  Fin'⇒Fin {suc i} (inj₁ tt) = zero
  Fin'⇒Fin {suc i} (inj₂ k) = suc (Fin'⇒Fin k)

  Fin-id : ∀ {n} (P : Fin n) → (Fin'⇒Fin ∘′ Fin⇒Fin') P ≡ P
  Fin-id zero = refl
  Fin-id (suc P) = cong suc (Fin-id P)

  Fin'-id : ∀ {n} (P : Fin' n) → (Fin⇒Fin' ∘′ Fin'⇒Fin) P ≡ P
  Fin'-id {zero} ()
  Fin'-id {suc i} (inj₁ tt) = refl
  Fin'-id {suc i} (inj₂ P) = cong inj₂ (Fin'-id P)

