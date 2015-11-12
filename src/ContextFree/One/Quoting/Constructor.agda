module ContextFree.One.Quoting.Constructor where

open import ContextFree.One.Params
open import ContextFree.One.Quoted
open import Data.Error
open Data.Error.Monad
open import Data.Fin using (Fin; #_; fromℕ≤)
open import Data.List using (List; []; _∷_; drop; map)
-- open import Data.Nat using (ℕ; zero; suc; _∸_; _≤?_; _≤_; z≤n; s≤s)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤?_; _≤_; z≤n; s≤s)
open import Data.Product using (_,_)
open import Data.Stream using (iterate)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (toList)
open import Function using (_∘′_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
open import Reflection
open import Stuff using (zipStream)

checkSort0 : Sort → Error ⊤
checkSort0 (lit zero) = ok tt
checkSort0 s = log "Sort is not `lit 0`" >> fail s

checkArginfovr : Arg-info → Error ⊤
checkArginfovr (arg-info visible relevant) = ok tt
checkArginfovr (arg-info _ _) = fail "Arg is not visible and relevant"

ℕtoFin : ∀{m S} → ℕ → S → Error (Fin m)
ℕtoFin n s = fromℕ≤ <$> decToError s (suc n ≤? _)

-- in : name of datatype, Type of the constructor, the number of params to use
-- out: list of SafeArgs
termToConstructor : (`dt : Name)(ct : Type)(pc : ℕ)(pc≤ : pc ≤ paramCount ct) →
                    Error (List (SafeArg {pc}))
termToConstructor `dt ct pc pc≤ = termToConstructor′
  where
  termToArg : (offset : ℕ) → Term → Error SafeArg
  termToArg offset (def f args) with f ≟-Name `dt | drop pc args
  termToArg offset (def f args) | yes p | []    = return Svar
  termToArg offset (def f args) | yes p | _ ∷ _ = fail "termToArg: self-reference has arguments"
  termToArg offset (def f args) | no ¬p | _     = fail "termToArg: reference to type that is not self"
  termToArg offset (var i []) = Spar <$> ℕtoFin (i ∸ offset)
            "termToArg: De Bruijn index too high, referencing something outside the data type?"
  termToArg offset otherwise = fail "termToArg: term not supported"

  quoteArg : ℕ → Sort → Type → Error SafeArg
  quoteArg offset s (el sarg t) = checkSort0 s >>
                                  checkSort0 sarg >>
                                  termToArg offset t

  checkTarget : Type → Error ⊤
  checkTarget (el s (def f args)) with f ≟-Name `dt | drop pc args
  checkTarget (el s (def f _)) | yes p | []    = checkSort0 s >> return tt
  checkTarget (el s (def f _)) | yes p | _ ∷ _ = fail "checkTarget: Indices in constructor target are not supported"
  checkTarget (el s (def f _)) | no ¬p | _     = fail "checkTarget: Invalid constructor target"
  checkTarget otherwise = fail "checkTarget: Invalid constructor target"

  termToConstructor′ : Error (List SafeArg)
  termToConstructor′ = let (pargs , ptarget) = takeParams ct pc pc≤ in
                       let (args , target) = getArgs ptarget in
                       checkTarget target >>
                       sequenceM (zipStream (λ { n (s , a) → quoteArg n s a })
                                            (iterate suc 0) args)

quoteConstructor : (`dt : Name)(c : Name)(pc : ℕ)(pc≤ : pc ≤ paramCount (type c)) →
                   Error (NamedSafeProduct {pc})
quoteConstructor `dt c pc pc≤ = _,_ c <$> termToConstructor `dt (type c) pc pc≤

module TestTermToConstructor where
  el0 : Term → Type
  el0 = el (lit 0)

  argvr : ∀{A} → A → Arg A
  argvr = arg (arg-info visible relevant)

  data Dummy : Set where
    dZ : Dummy
    dS : Dummy → Dummy

  testZ : ok ((quote dZ) , []) ≡ quoteConstructor (quote Dummy) (quote dZ) 0 z≤n
  testZ = refl

  testS : ok ((quote dS) , Svar ∷ []) ≡ quoteConstructor (quote Dummy) (quote dS) 0 z≤n
  testS = refl

  data Dummy2 (A : Set) : Set where
    dRec : A → Dummy2 A

  testRec : ok (quote dRec , Spar (# 0) ∷ []) ≡ quoteConstructor (quote Dummy2) (quote dRec) 1 (s≤s z≤n)
  testRec = refl

  data Dummy3 (A B : Set) : Set where
    dPair : A → B → Dummy3 A B
    dMulti : B → B → Dummy2 A → Dummy3 A B

  testPair : ok (quote dPair , Spar (# 1) ∷ Spar (# 0) ∷ [])
    ≡ quoteConstructor (quote Dummy3) (quote dPair) 2 (s≤s (s≤s z≤n))
  testPair = refl

  -- type of dMulti : {A B : Set} → B → B → Dummy2 A → Dummy3 A B
  -- testMulti : ok (quote dMulti ,
  --                 SK (var 0 []) ∷
  --                 SK (var 0 []) ∷
  --                 SK (def (quote Dummy2) (argvr (var 1 []) ∷ [])) ∷ [])
  --             ≡ quoteConstructor (quote Dummy3) (quote dMulti) (# 2)
  -- testMulti = refl
