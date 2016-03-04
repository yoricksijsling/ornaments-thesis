module ContextFree.One.Unquoting where

open import Common
open import Reflection
open import TC
open import ContextFree.One.Params
open import ContextFree.One.Quoted

-- given some NamedSafeDatatype, produce the types of all the constructors..

-- private
--   open import Stuff using (zipNatsDown)
--   -- open import ContextFree.One.EmbeddingProjection using (paramArgs)
--   paramArgs : ∀{tp}(offset : Nat){pc : Nat} → Vec Param pc → List (Arg ⟦ tp ⟧tp)
--   paramArgs {tp} offset = zipNatsDown offset tm ∘ vecToList
--     where tm : Nat → Param → Arg ⟦ tp ⟧tp
--           tm offset (param₀ v s) = arg (arg-info v relevant) (`var₀ offset s)

index! : ∀ {a} {A : Set a} → (xs : List A) → Fin (length xs) → A
index! [] ()
index! (x ∷ _) zero = x
index! (_ ∷ xs) (suc i) = index! xs i

-- kind of inverse of parseConstructor
cType : (nsdt : SafeDatatype)(`dt : Name)(i : Fin (length (SafeDatatype.sop nsdt))) → Term
cType (mk pc params sop) `dt i = cType′ 0 (index! sop i)
  where
  argToTerm : (offset : Nat) → SafeArg {pc} → Term
  argToTerm offset (Spar k) = var (finToNat k +N offset) []
  argToTerm offset Srec = def `dt (paramVars offset params)

  cType′ : (offset : Nat) → SafeProduct {pc} → Term
  cType′ offset [] = def `dt (paramVars offset params)
  cType′ offset (a ∷ nsp) = argToTerm offset a `→ cType′ (suc offset) nsp

macro 
  _as_∋_ : (nsdt : SafeDatatype) → Name → (i : Fin (length (SafeDatatype.sop nsdt))) → Tactic
  sdt as `dt ∋ i = give (cType sdt `dt i)

module TestCT where
  open import ContextFree.One.Quoting

  data Dummy : Set where
    dZ : Dummy
    dS : Dummy → Dummy

  qDummy : SafeDatatype
  qDummy = fst $ unnameSafeDatatype $ quoteDatatypeᵐ Dummy

  test-dZ : qDummy as Dummy ∋ 0 ≡ Dummy
  test-dZ = refl

  test-dS : qDummy as Dummy ∋ 1 ≡ (Dummy → Dummy)
  test-dS = refl  
  
  data Dummy2 (A : Set) : Set where
    dRec : A → Dummy2 A

  qDummy2 : SafeDatatype
  qDummy2 = fst $ unnameSafeDatatype $ quoteDatatypeᵐ Dummy2

  test-dRec : ∀ (A : Set) → qDummy2 as Dummy2 ∋ 0 ≡ (A → Dummy2 A)
  test-dRec A = refl

  data Dummy3 (A B : Set) : Set where
    dPair : A → B → Dummy3 A B

  qDummy3 : SafeDatatype
  qDummy3 = fst $ unnameSafeDatatype $ quoteDatatypeᵐ Dummy3

  test-dPair : ∀ (A B : Set) → qDummy3 as Dummy3 ∋ 0 ≡ (A → B → Dummy3 A B)
  test-dPair A B = refl
