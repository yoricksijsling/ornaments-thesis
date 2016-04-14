
module Cx.Examples.Vec where

open import Common
open import Cx.Named
open import Cx.Quotable.Core
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
  desc : DatDesc (Nat × ⊤) (ε ▷₁ (λ γ → Set)) 2
  desc = "nil"  ∣ ι (λ _ → 0 , tt)
       ⊕ "cons" ∣ "n" / (λ γ → Nat)
                ⊗ "x" / (λ γ → top (pop γ))
                ⊗ "xs" /rec (λ γ → top (pop γ) , tt)
                ⊗ ι (λ γ → suc (top (pop γ)) , tt)
       ⊕ `0

  to : ∀ {A n} → MyVec A n → μ desc (tt , A) (n , tt)
  to nil-α = nil-β
  to (cons-α n x xs) = cons-β n x (to xs)

  from : ∀ {A n} → μ desc (tt , A) (n , tt) → MyVec A n
  from nil-β = nil-α
  from (cons-β n x xs) = cons-α n x (from xs)
  from absurd-β

  re : ∀ A n → Quotable (MyVec A n)
  re A n = mk desc to from


module Auto where
  a : SomeDatDesc
  a = quoteDatatypeᵐ MyVec

  test-desc : SomeDatDesc.desc a ≡ Manually.desc
  test-desc = refl
