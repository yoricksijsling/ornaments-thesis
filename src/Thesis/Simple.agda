-- {-# OPTIONS --no-positivity-check #-}

module Thesis.Simple where

open import Common
open import Cx.Simple

--------------------
-- Introduction

listDesc : (A : Set) → DatDesc 2
listDesc A = ι ⊕ (λ γ → A) ⊗ rec-⊗ ι ⊕ `0

-- Σ Nat isLessThan7
IsLessThan7 : Nat → Set
IsLessThan7 n = n < 7
lt7Desc : DatDesc 1
lt7Desc = (λ γ → Nat) ⊗ (λ γ → IsLessThan7 (top γ)) ⊗ ι ⊕ `0
lt7Desc′ : DatDesc 1
lt7Desc′ = const Nat ⊗ IsLessThan7 ∘ top ⊗ ι ⊕ `0

IsShorter : {A : Set} → List A → Nat → Set
IsShorter _ zero = ⊥
IsShorter [] (suc n) = ⊤
IsShorter (_ ∷ xs) (suc n) = IsShorter xs n

shorterDesc : ∀{A} → DatDesc 1
shorterDesc {A} = const (List A) ⊗ const Nat ⊗
  (λ γ → IsShorter (top (pop γ)) (top γ)) ⊗ ι ⊕ `0

lt7-insertFin : DatOrn lt7Desc
lt7-insertFin = -⊗ Fin ∘ top +⊗ -⊗ ι ⊕ `0

test-lt7-insertFin : ornToDesc lt7-insertFin ≡
  (const Nat ⊗ Fin ∘ top ⊗ IsLessThan7 ∘ top ∘ pop ⊗ ι ⊕ `0)
test-lt7-insertFin = refl

-- nbsDesc : DatDesc 1
-- nbsDesc = (λ γ → List Bool) ⊗ (λ γ → Nat) ⊗ ι ⊕ `0
-- nbs→shorter : DatOrn nbsDesc
-- nbs→shorter = -⊗ -⊗ (λ δ → IsShorter (top (pop δ)) (top δ)) +⊗ ι ⊕ `0


--------------------
-- Contexts

-- See simplifiedcontexts

ShorterEnv : {A : Set} → Set
ShorterEnv {A} = ⊤′ ▶₀ (λ γ → List A) ▶₀ (λ γ → Nat) ▶₀
  (λ γ → IsShorter (top (pop γ)) (top γ))

shorterEnv : ShorterEnv {Nat}
shorterEnv = ((tt , (3 ∷ 4 ∷ [])) , 10) , _

ShorterCx : {A : Set} → Cx₀
ShorterCx {A} = ε ▷′ List A ▷′ Nat ▷ (λ γ → IsShorter (top (pop γ)) (top γ))

test-ShorterCx : ∀{A} → ⟦ ShorterCx {A} ⟧ ≡ ShorterEnv {A}
test-ShorterCx = refl


--------------------
-- Descriptions


pairDesc : (A : Set) (B : A → Set) → DatDesc 1
{-
pairDesc₁ pairDesc₂ pairDesc₃ : (A : Set) (B : A → Set) → DatDesc 1

pairDesc₁ A B = {!0!} ⊕ `0
-- |?0 : ConDesc ε|

pairDesc₂ A B = const A ⊗ {!1!} ⊕ `0
-- |?1 : ConDesc (ε ▷′ A)|

pairDesc₃ A B = const A ⊗ {!2!} ⊗ ι ⊕ `0
-- |?2 : ⟦ ε ▷′ A ⟧ → Set|
-- |?2 : ⊤′ ▶₀ const A → Set|
-}
pairDesc A B = const A ⊗ B ∘ top ⊗ ι ⊕ `0

pair-to : {A : Set}{B : A → Set} → Σ A B → μ (pairDesc A B)
pair-to (x , y) = ⟨ 0 , x , y , tt ⟩


open import Thesis.SigmaDesc

shorterDescΣ : {A : Set} → DescΣ
shorterDescΣ {A} = σ (List A) λ xs → σ Nat λ n →
  σ (IsShorter xs n) λ _ → ι
