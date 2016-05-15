
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
  vdesc : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
  vdesc = ι (λ _ → tt , 0)
       ⊕ "n" / (λ γ → Nat)
                ⊗ "x" / top ∘ pop
                ⊗ "xs" /rec (λ γ → tt , top (pop γ))
                ⊗ ι (λ γ → tt , suc (top (pop γ)))
       ⊕ `0

  vto : ∀ {A n} → MyVec A n → μ vdesc (tt , A) (tt , n)
  vto nil-α = nil-β
  vto (cons-α n x xs) = cons-β n x (vto xs)

  vfrom : ∀ {A n} → μ vdesc (tt , A) (tt , n) → MyVec A n
  vfrom nil-β = nil-α
  vfrom (cons-β n x xs) = cons-α n x (vfrom xs)
  vfrom absurd-β

  vecHasDesc : ∀ {A n} → HasDesc (MyVec A n)
  vecHasDesc = mk vdesc vto vfrom


module Auto where
  unquoteDecl quotedVec vecHasDesc = deriveHasDesc quotedVec vecHasDesc (quote MyVec)

  test-desc : QuotedDesc.desc quotedVec ≡ Manually.vdesc
  test-desc = refl


  test-to : ∀ {A n} → (xs : MyVec A n) → Manually.vto xs ≡ to xs
  test-to nil-α = refl
  test-to (cons-α n x xs) = cong (cons-β n x) (test-to xs)

  test-from : ∀ {A n} → (xs : μ Manually.vdesc (tt , A) (tt , n)) → Manually.vfrom xs ≡ from xs
  test-from nil-β = refl
  test-from (cons-β n x xs) = cong (cons-α n x) (test-from xs)
  test-from absurd-β
