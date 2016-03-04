module ContextFree.Multi.Quoting.Constructor where

open import Builtin.Reflection
open import Common
open import Container.Traversable
open import TC

open import ContextFree.Multi.Params
open import ContextFree.Multi.Quoted
open import Stuff using (zipNats)

private
  SomeNamedSafeProduct : Set
  SomeNamedSafeProduct = Σ Nat (λ pc → NamedSafeProduct {pc})

checkArginfovr : ArgInfo → TC ⊤
checkArginfovr (arg-info visible relevant) = return tt
checkArginfovr (arg-info _ _) = fail "Arg is not visible and relevant"

NatToFin : ∀{m} → Nat → String → TC (Fin m)
NatToFin {m} n s = iguard (natToFin n) s

-- in : name of datatype, Type of the constructor, the number of params to use
-- out: list of SafeArgs
parseConstructor : (`dt : Name)(pc : Nat)(cty : Type) → TC (List (SafeArg {pc}))
parseConstructor `dt pc = parseConstructor′
  where
  parseArg : (offset : Nat) → Term → TC SafeArg
  parseArg offset (def f args) with f == `dt | drop pc args
  parseArg offset (def f args) | yes p | []    = return Srec
  parseArg offset (def f args) | yes p | _ ∷ _ = fail "parseArg: self-reference has arguments"
  parseArg offset (def f args) | no ¬p | _     = fail "parseArg: reference to type that is not self"
  parseArg offset (var i []) = Spar <$> NatToFin (i -N offset)
            "parseArg: De Bruijn index too high, referencing something outside the data type?"
  parseArg offset otherwise = fail "parseArg: term not supported"

  checkTarget : Type → TC ⊤
  checkTarget (def f args) with f == `dt | drop pc args
  checkTarget (def f _) | yes p | [] = return tt
  checkTarget (def f _) | yes p | _ ∷ _ = fail "checkTarget: Indices in constructor target are not supported"
  checkTarget (def f _) | no ¬p | _ = fail "checkTarget: Invalid constructor target"
  checkTarget otherwise = fail "checkTarget: Invalid constructor target"

  parseConstructor′ : Type → TC (List SafeArg)
  parseConstructor′ cty =
    (fromMaybe ("parseConstructor′: Took to many parameters") (dropParams cty pc)) >>= λ cty′ →
    let args,target = getArgs cty′ in
    checkTarget (snd args,target) >>
    mapM id (zipNats parseArg (fst args,target))

quoteConstructor : (`dt : Name)(pc : Nat)(`c : Name) → TC NamedSafeProduct
quoteConstructor `dt pc `c =
  getType `c >>= λ cty →
  parseConstructor `dt pc cty >>= λ as →
  return (`c , as)

macro
  quoteConstructorᵐ : (`dt : Name)(pc : Nat)(`c : Name) → Tactic
  quoteConstructorᵐ `dt pc `c = runTC (quoteConstructor `dt pc `c)

module TestTermToConstructor where
  data Dummy : Set where
    dZ : Dummy
    dS : Dummy → Dummy

  testZ : (quote dZ , []) ≡ quoteConstructorᵐ Dummy 0 dZ
  testZ = refl

  testS : (quote dS , Srec ∷ []) ≡ quoteConstructorᵐ Dummy 0 dS
  testS = refl

  data Dummy2 (A : Set) : Set where
    dRec : A → Dummy2 A

  testRec : (quote dRec , Spar 0 ∷ []) ≡ quoteConstructorᵐ Dummy2 1 dRec
  testRec = refl

  data Dummy3 (A B : Set) : Set where
    dPair : A → B → Dummy3 A B
    dMulti : B → B → Dummy2 A → Dummy3 A B

  -- testPair : ok (quote dPair , Spar (# 1) ∷ Spar (# 0) ∷ [])
  --   ≡ quoteConstructor (quote Dummy3) (quote dPair) 2 (s≤s (s≤s z≤n))
  -- testPair : (2 , quote dPair , Spar 1 ∷ Spar 0 ∷ []) ≡ quoteConstructorᵐ Dummy3 dPair

  testPair : (quote dPair , Spar 1 ∷ Spar 0 ∷ []) ≡ quoteConstructorᵐ Dummy3 2 dPair
  testPair = refl

  -- type of dMulti : {A B : Set} → B → B → Dummy2 A → Dummy3 A B
  -- testMulti : ok (quote dMulti ,
  --                 SK (var 0 []) ∷
  --                 SK (var 0 []) ∷
  --                 SK (def (quote Dummy2) (argvr (var 1 []) ∷ [])) ∷ [])
  --             ≡ quoteConstructor (quote Dummy3) (quote dMulti) (# 2)
  -- testMulti = refl
