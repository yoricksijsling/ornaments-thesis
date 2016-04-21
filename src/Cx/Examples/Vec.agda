
module Cx.Examples.Vec where

open import Common
open import Cx.Named
open import Cx.HasDesc.Core
open import Cx.Quoting

data MyVec (A : Set) : Nat → Set where
  nil : MyVec A 0
  cons : ∀ n → (x : A) → (xs : MyVec A n) → MyVec A (suc n)

pattern nil-α = nil
pattern nil-β = ⟨ zero , refl ⟩
pattern cons-α n x xs = cons n x xs
pattern cons-β n x xs = ⟨ suc zero , n , x , xs , refl ⟩
pattern absurd-β = ⟨ suc (suc ()) , _ ⟩

module Manually where
  -- desc : DatDesc (Nat × ⊤) (ε ▷₁ (λ γ → Set)) 2
  desc : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
  desc = ι (λ _ → tt , 0)
       ⊕ "n" / (λ γ → Nat)
                ⊗ "x" / top ∘ pop
                ⊗ "xs" /rec (λ γ → tt , top (pop γ))
                ⊗ ι (λ γ → tt , suc (top (pop γ)))
       ⊕ `0

  to : ∀ {A n} → MyVec A n → μ desc (tt , A) (tt , n)
  to nil-α = nil-β
  to (cons-α n x xs) = cons-β n x (to xs)

  from : ∀ {A n} → μ desc (tt , A) (tt , n) → MyVec A n
  from nil-β = nil-α
  from (cons-β n x xs) = cons-α n x (from xs)
  from absurd-β

  re : ∀ A n → HasDesc (MyVec A n)
  re A n = mk (quote MyVec) (quote MyVec.nil ∷ quote MyVec.cons ∷ [])
           desc to from


module Auto where
  q : QuotedDesc
  q = quoteDatatypeᵐ MyVec

  test-desc : QuotedDesc.desc q ≡ Manually.desc
  test-desc = refl
