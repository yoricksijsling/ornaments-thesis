
module Thesis.Implementation where

open import Common
open import Reflection
open import Cx.HasDesc
import Cx.Quoting.Constructor as QC

quoteConstructor : (`dt : Name) (#p : Nat) → ∀ I Γ → (`c : Name) → TC (ConDesc I Γ)
quoteConstructor = QC.quoteConstructor

macro
  quoteConstructorᵐ : (`dt : Name) (#p : Nat) (I : Cx) (Γ : Cx) (`c : Name) → Tactic
  quoteConstructorᵐ `dt #p I Γ `c = evalTC (quoteConstructor `dt #p I Γ `c)

testSuc : quoteConstructorᵐ Nat 0 ε ε Nat.suc ≡ (_ /rec (λ γ → tt) ⊗ ι (λ γ → tt))
testSuc = refl

data Pair (A B : Set) : Set where
  pair : A → B → Pair A B

testPair : quoteConstructorᵐ Pair 2 ε (ε ▷₁′ Set ▷₁′ Set) pair
  ≡ ("_" / (top ∘ pop) ⊗ "_" / (top ∘ pop) ⊗ ι (λ γ → tt))
testPair = refl


-- data Pair (A : Set) (B : A → Set) : Set where
--   pair : (a : A) → B a → Pair A B

-- testPair : quoteConstructorᵐ Pair 2 ε (ε ▷₁′ Set ▷₁ (λ γ → top γ → Set)) pair
--   ≡ ("a" / (λ γ → top (pop γ)) ⊗ "_" / (λ γ → top (pop γ) (top γ)) ⊗ ι (λ γ → tt))
-- testPair = refl
