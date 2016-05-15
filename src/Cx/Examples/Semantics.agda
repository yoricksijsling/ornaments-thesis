
-- Semantics-preserving operations

module Cx.Examples.Semantics where

open import Common
open import Reflection
open import Cx.HasDesc
open import Cx.GenericOperations
open import Cx.Unquoting

data Ty : Set where
  `Nat : Ty
  `Bool : Ty

⟦_⟧Ty : Ty → Set
⟦ `Nat ⟧Ty = Nat
⟦ `Bool ⟧Ty = Bool

data Exp : Ty → Set where
  `nat : Nat → Exp `Nat
  `≤ : Exp `Nat → Exp `Nat → Exp `Bool
  `+ : Exp `Nat → Exp `Nat → Exp `Nat
  `if : ∀ ty → Exp `Bool → Exp ty → Exp ty → Exp ty

unquoteDecl quotedExp expHasDesc =
  deriveHasDesc quotedExp expHasDesc (quote Exp)
expDesc : DatDesc (ε ▷′ Ty) ε 4
expDesc = QuotedDesc.desc quotedExp

SemAlg : Alg expDesc tt (λ i → ⟦ top i ⟧Ty)
SemAlg (zero , x , refl) = x
SemAlg (suc zero , x , y , refl) = x ≤? y
SemAlg (suc (suc zero) , x , y , refl) = x + y
SemAlg (suc (suc (suc zero)) , _ , c , x , y , refl) = if c then x else y
SemAlg (suc (suc (suc (suc ()))) , _)

⟦_⟧Exp : ∀{ty} → Exp ty → ⟦ ty ⟧Ty
⟦_⟧Exp tm = gfold SemAlg tm

semExpOrn : Orn _ _ expDesc
semExpOrn = algOrn SemAlg

semExpDesc : DatDesc (ε ▷′ Ty ▷ (λ γ → ⟦ top γ ⟧Ty)) ε 4
semExpDesc = ornToDesc semExpOrn

-- Unquoting datatypes is somewhat verbose right now:
data SemExp : unquoteDat semExpDesc where
  `nat : unquoteCon semExpDesc 0 SemExp
  `≤ : unquoteCon semExpDesc 1 SemExp
  `+ : unquoteCon semExpDesc 2 SemExp
  `if : unquoteCon semExpDesc 3 SemExp
unquoteDecl quotedSemExp semExpHasDesc =
  deriveHasDescExisting quotedSemExp semExpHasDesc (quote SemExp) semExpDesc
-- Ideally, one would be able to define datatypes within TC:
--   unquoteDecl quotedSemExp semExpHasDesc SemExp `nat `≤ `+ `if =
--     unquoteDatatype semExpDesc quotedSemExp semExpHasDesc SemExp (`nat ∷ `≤ ∷ `+ ∷ `if)


-- (if 3 ≤ 4 then 10 else 20) + 7
example-exp : Exp `Nat
example-exp = `+ (`if _ (`≤ (`nat 3) (`nat 4)) (`nat 0) (`nat 20)) (`nat 7)

forgetSem : ∀{ty v}(t : SemExp ty v) → Exp ty
forgetSem = gforget semExpOrn

-- It is possible to build this automatically, because we used an algebra.
rememberSem : ∀{ty}(t : Exp ty) → SemExp ty ⟦ t ⟧Exp
rememberSem (`nat x) = `nat x
rememberSem (`≤ t₁ t₂) = `≤ _ (rememberSem t₁) _ (rememberSem t₂)
rememberSem (`+ t₁ t₂) = `+ _ (rememberSem t₁) _ (rememberSem t₂)
rememberSem (`if _ c t₁ t₂) = `if _ _ (rememberSem c) _ (rememberSem t₁) _ (rememberSem t₂)

optimise-0+ : ∀{ty v} → SemExp ty v → SemExp ty v
optimise-0+ (`nat n) = `nat n
optimise-0+ (`≤ _ x _ y) = `≤ _ (optimise-0+ x) _ (optimise-0+ y)
optimise-0+ (`+ 0 x _ y) = y
optimise-0+ (`+ _ x _ y) = `+ _ (optimise-0+ x) _ (optimise-0+ y)
optimise-0+ (`if _ _ c _ t _ f) = `if _ _ (optimise-0+ c) _ (optimise-0+ t) _ (optimise-0+ f)

optimise-0+′ : ∀{ty} → Exp ty → Exp ty
optimise-0+′ = forgetSem ∘ optimise-0+ ∘ rememberSem

optimise-0+-example : optimise-0+′ example-exp ≡ `nat 7
optimise-0+-example = refl

