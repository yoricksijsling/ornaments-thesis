
module Thesis.Simple where

open import Common
open import Cx.Simple

--------------------
-- Introduction

listDesc : (A : Set) → DatDesc 2
listDesc A = ι ⊕ (λ γ → A) ⊗ rec-⊗ ι ⊕ `0


---

IsLessThan7 : Nat → Set
IsLessThan7 n = n < 7

data Lt7 : Set where
  lt7 : (n : Nat) → IsLessThan7 n → Lt7

lt7Desc : DatDesc 1
lt7Desc = (λ γ → Nat) ⊗ (λ γ → IsLessThan7 (top γ)) ⊗ ι ⊕ `0

module ContextCombinators where
  postulate
    Γ : Cx₀
    f : Nat → Bool → String
    x : ⟦ Γ ⟧ → Nat
    y : ⟦ Γ ⟧ → Bool

  fxy₁ fxy₂ fxy₃ : ⟦ Γ ⟧ → String
  fxy₁ = λ γ → f (x γ) (y γ)
  fxy₂ = const f <S> x <S> y
  fxy₃ = f <KS> x <S> y

lt7Desc′ : DatDesc 1
lt7Desc′ = const Nat ⊗ IsLessThan7 <KS> top ⊗ ι ⊕ `0

---

IsShorter : {A : Set} → List A → Nat → Set
IsShorter _ zero = ⊥
IsShorter [] (suc n) = ⊤
IsShorter (_ ∷ xs) (suc n) = IsShorter xs n

data Shorter (A : Set) : Set where
  shorter : (xs : List A) → (n : Nat) → IsShorter xs n → Shorter A

shorterDesc : ∀{A} → DatDesc 1
shorterDesc {A} = const (List A) ⊗ const Nat ⊗
  IsShorter <KS> top ∘ pop <S> top ⊗ ι ⊕ `0


--------------------
-- Contexts

-- See simplifiedcontexts

ShorterEnv : {A : Set} → Set
ShorterEnv {A} = ⊤′ ▶₀ const (List A) ▶₀ const Nat ▶₀
  IsShorter <KS> top ∘ pop <S> top

shorterEnv : ShorterEnv {Nat}
shorterEnv = ((tt , (3 ∷ 4 ∷ [])) , 10) , _

ShorterCx : {A : Set} → Cx₀
ShorterCx {A} = ε ▷′ List A ▷′ Nat ▷ IsShorter <KS> top ∘ pop <S> top

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
pairDesc A B = const A ⊗ B <KS> top ⊗ ι ⊕ `0

pair-to : {A : Set}{B : A → Set} → Σ A B → μ (pairDesc A B)
pair-to (x , y) = ⟨ 0 , x , y , tt ⟩


--------------------
-- Ornaments

postulate
  IsOdd : Nat → Set

lt7odd : DatOrn lt7Desc′
lt7odd = -⊗ IsOdd <KS> top +⊗ -⊗ ι ⊕ `0

test-lt7odd : ornToDesc lt7odd ≡
  (const Nat ⊗ IsOdd <KS> top ⊗ IsLessThan7 <KS> top ∘ pop ⊗ ι ⊕ `0)
test-lt7odd = refl

postulate
  proof-that-3<7 : (3 ofType Nat) < 7
  proof-that-3-is-odd : IsOdd 3

ex-lt7odd : μ (ornToDesc lt7odd)
ex-lt7odd = ⟨ 0 , 3 , proof-that-3-is-odd , proof-that-3<7 , tt ⟩

forget-lt7odd : forget lt7odd ex-lt7odd ≡ ⟨ 0 , 3 , proof-that-3<7 , tt ⟩
forget-lt7odd = refl


--------------------
-- Discussion

open import Thesis.SigmaDesc

shorterDescΣ : {A : Set} → DescΣ
shorterDescΣ {A} = σ (List A) λ xs → σ Nat λ n →
  σ (IsShorter xs n) λ _ → ι
