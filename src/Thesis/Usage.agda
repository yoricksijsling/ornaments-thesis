module Thesis.Usage where

open import Common hiding (List; length; Vec; vecToList)
open import Reflection
open import Cx.HasDesc
open import Cx.GenericOperations
open import Cx.Named.Mutations
open import Cx.Unquoting

-- data Nat : Set where
--   zero : Nat
--   suc : Nat → Nat

unquoteDecl quotedNat NatHasDesc =
  deriveHasDesc quotedNat NatHasDesc (quote Nat)

natDesc : Desc ε ε _
natDesc = QuotedDesc.desc quotedNat

natTo : Nat → μ natDesc tt tt
natTo = to

natFrom : μ natDesc tt tt → Nat
natFrom = from

--

data List (A : Set) : Set where
  nil : List A
  cons : (x : A) → (xs : List A) → List A

unquoteDecl quotedList ListHasDesc =
  deriveHasDesc quotedList ListHasDesc (quote List)

listDesc : Desc ε (ε ▷₁′ Set) _
listDesc = QuotedDesc.desc quotedList

listTo : ∀{A} → List A → μ listDesc (tt , A) tt
listTo = to

listFrom : ∀{A} → μ listDesc (tt , A) tt → List A
listFrom = from

nat-id : Nat → Nat
nat-id = gdepth

nat-id-ok : ∀ n → nat-id n ≡ n
nat-id-ok zero = refl
nat-id-ok (suc n) = cong suc (nat-id-ok n)

-- gdepth : ∀{A} → {{R : HasDesc A}} → A → Nat
length : ∀{A} → List A → Nat
length = gdepth

length′ : ∀{A} → List A → Nat
length′ = gfold (depthAlg listDesc)

countBoolsAlg : Alg listDesc (tt , Bool) (λ x → Nat)
countBoolsAlg (zero , refl) = 0
countBoolsAlg (suc zero , x , xs , refl) = if x then suc xs else xs
countBoolsAlg (suc (suc ()) , _)

countBools : List Bool → Nat
countBools = gfold countBoolsAlg

--

nat→list : Orn _ _ natDesc
nat→list = renameArguments 1 (just "xs" ∷ [])
 >>⁺ addParameterArg 1 "x"

test-nat→list : ornToDesc nat→list ≡ listDesc
test-nat→list = refl

--


list→vec : Orn _ _ listDesc
list→vec = algOrn (depthAlg listDesc)

vecDesc : Desc (ε ▷′ Nat) (ε ▷₁′ Set) _
vecDesc = ornToDesc list→vec

data Vec (A : Set) : unquoteDat vecDesc where
  nil : unquoteCon vecDesc 0 Vec
  cons : unquoteCon vecDesc 1 Vec
unquoteDecl quotedVec VecHasDesc =
  deriveHasDescExisting quotedVec VecHasDesc (quote Vec) vecDesc

vecTo : ∀{A n} → Vec A n → μ vecDesc (tt , A) (tt , n)
vecTo = to

vecToList : ∀{A n} → Vec A n → List A
vecToList = gforget list→vec

-- fromList : ∀{A} → List A → Vec A (length n)
-- fromList = gremember (depthAlg listDesc)

