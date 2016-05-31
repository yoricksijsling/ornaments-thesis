
module Thesis.SigmaDesc where

open import Common

data DescΣ : Set₁ where
  ι : DescΣ
  σ : (S : Set) → (xs : S → DescΣ) → DescΣ
  rec-×_ : (xs : DescΣ) → DescΣ

⟦_⟧DescΣ : DescΣ → Set → Set
⟦ ι ⟧DescΣ X = ⊤
⟦ σ S xs ⟧DescΣ X = Σ S λ s → ⟦ xs s ⟧DescΣ X
⟦ rec-× xs ⟧DescΣ X = X × ⟦ xs ⟧DescΣ X

instance DescΣ-semantics : Semantics DescΣ
         DescΣ-semantics = record { ⟦_⟧ = ⟦_⟧DescΣ }
{-# DISPLAY ⟦_⟧DescΣ x = ⟦_⟧ x #-}

data μΣ (D : DescΣ) : Set where
  ⟨_⟩ : ⟦ D ⟧DescΣ (μΣ D) → μΣ D

emptyDescΣ : DescΣ
emptyDescΣ = σ ⊥ ⊥-elim

pairDescΣ : (A B : Set) → DescΣ
pairDescΣ A B = σ A λ a → σ B λ b → ι

eitherDescΣ : (A B : Set) → DescΣ
eitherDescΣ A B = σ (Fin 2) λ
  { zero → σ A λ a → ι
  ; (suc zero) → σ B λ b → ι
  ; (suc (suc ())) }

eitherDescΣ-left : ∀{A B} → A → μΣ (eitherDescΣ A B)
eitherDescΣ-left x = ⟨ 0 , x , tt ⟩
eitherDescΣ-right : ∀{A B} → B → μΣ (eitherDescΣ A B)
eitherDescΣ-right x = ⟨ 1 , x , tt ⟩

data OrnΣ : (D : DescΣ) → Set₁ where
  ι : OrnΣ ι
  σ : (S : Set) → ∀{xs} (xs⁺ : (s : S) → OrnΣ (xs s)) → OrnΣ (σ S xs)
  rec-×_ : ∀{xs} (xs⁺ : OrnΣ xs) → OrnΣ (rec-× xs)
  insert-σ : (S : Set) → ∀{xs} → (xs⁺ : S → OrnΣ xs) → OrnΣ xs
  delete-σ : ∀{S xs} → (s : S) → (xs⁺ : OrnΣ (xs s)) → OrnΣ (σ S xs)

ornToDescΣ : ∀{D} → OrnΣ D → DescΣ
ornToDescΣ ι = ι
ornToDescΣ (σ S xs⁺) = σ S (λ s → ornToDescΣ (xs⁺ s))
ornToDescΣ (rec-× xs⁺) = rec-× (ornToDescΣ xs⁺)
ornToDescΣ (insert-σ S xs⁺) = σ S (λ s → ornToDescΣ (xs⁺ s))
ornToDescΣ (delete-σ s xs⁺) = ornToDescΣ xs⁺

natDescΣ : DescΣ
natDescΣ = σ (Fin 2) λ
  { zero → ι
  ; (suc zero) → rec-× ι
  ; (suc (suc ())) }

-- listDescΣ : (A : Set) → DescΣ
-- listDescΣ A = σ (Fin 2) λ
--   { zero → ι
--   ; (suc zero) → σ A λ a → rec-× ι
--   ; (suc (suc ())) }

nat→listΣ : (A : Set) → OrnΣ natDescΣ
nat→listΣ A = σ (Fin 2) λ
  { zero → ι
  ; (suc zero) → insert-σ A λ a → rec-× ι
  ; (suc (suc ())) }
-- test-nat→listΣ : (ext : ∀{a b} → Extensionality a b) → ∀{A} → ornToDescΣ (nat→listΣ A) ≡ listDescΣ A
-- test-nat→listΣ ext {A} = cong (σ (Fin 2)) $ ext λ { zero → refl
--                                                    ; (suc zero) → refl
--                                                    ; (suc (suc ())) }

boolsDescΣ : DescΣ
boolsDescΣ = σ Nat rest
  where rest : Nat → DescΣ
        rest zero = ι
        rest (suc n) = σ Bool λ _ → rest n

boolsDescΣ-example : μΣ boolsDescΣ
boolsDescΣ-example = ⟨ 3 , true , false , true , tt ⟩


-- Swap the constructors of naturals
swapnatΣ : OrnΣ natDescΣ
swapnatΣ = insert-σ (Fin 2) λ
  { zero → delete-σ 1 (rec-× ι)
  ; (suc zero) → delete-σ 0 ι
  ; (suc (suc ())) }

{-
swapnat : DatOrn natDesc
swapnat = recons 2 λ
  { zero → 1 , rec-⊗ ι
  ; (suc zero) → 0 , ι
  ; (suc (suc ())) }
-}
