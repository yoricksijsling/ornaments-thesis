
module Cx.Examples.Vec where

open import Common
open import Reflection
open import Cx.HasDesc
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

  vecHasDesc : ∀ {A n} → HasDesc (MyVec A n)
  vecHasDesc = mk desc to from


module Auto where
  open HasDesc {{...}} using (to; from)

  unquoteDecl quotedVec vecHasDesc = deriveHasDesc quotedVec vecHasDesc (quote MyVec)

  test-desc : QuotedDesc.desc quotedVec ≡ Manually.desc
  test-desc = refl


  test-to : ∀ {A n} → (xs : MyVec A n) → Manually.to xs ≡ to xs
  test-to nil-α = refl
  test-to (cons-α n x xs) = cong (cons-β n x) (test-to xs)

  test-from : ∀ {A n} → (xs : μ Manually.desc (tt , A) (tt , n)) → Manually.from xs ≡ from xs
  test-from nil-β = refl
  test-from (cons-β n x xs) = cong (cons-α n x) (test-from xs)
  test-from absurd-β
