module ContextFree.One.Quoting.Constructor where

open import Data.Fin using (Fin; zero; suc; toℕ; #_)
open import Data.List using (List; []; _∷_; drop; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; uncurry′)
open import Data.Stream using (iterate)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (toList)
open import Function using (_∘′_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
open import Reflection

open import ContextFree.One.Quoted
open import Data.Error
open Data.Error.Monad
open import Stuff using (zipStream)
open import TypeArgs

checkSort0 : Sort → Error ⊤
checkSort0 (lit zero) = ok tt
checkSort0 s = log "Sort is not `lit 0`" >> fail s

checkArginfovr : Arg-info → Error ⊤
checkArginfovr (arg-info visible relevant) = ok tt
checkArginfovr (arg-info _ _) = fail "Arg is not visible and relevant"

dropIndex : ℕ → SafeArg → Error SafeArg
dropIndex (suc n) (SK t) = dropIndex₁ t >>= dropIndex n ∘′ SK
  where
  dropIndex₁ : Term → Error Term
  dropIndex₁ (var (suc x) []) = return (var x [])
  dropIndex₁ (def f args) = log "dropIndex: term not supported" >> fail (def f args)
  dropIndex₁ otherwise = log "dropIndex: term not supported" >> fail otherwise
dropIndex n otherwise = return otherwise

termToConstructor : Name → (t : Type) → Fin (suc (argCount t)) → Error (List SafeArg)
termToConstructor self ct p = termToConstructor′
  where
  termToArg : Term → Error SafeArg
  termToArg (def f args) with f ≟-Name self | drop (toℕ p) args
  termToArg (def f args) | yes p | []    = return Svar
  termToArg (def f args) | yes p | _ ∷ _ = fail "termToArg: self-reference has arguments"
  termToArg (def f args) | no ¬p | _     = return (SK (def f args))
  termToArg otherwise = return (SK otherwise)

  quoteArg : ℕ → Sort → Arg Type → Error SafeArg
  quoteArg n s (arg i (el sarg t)) = checkSort0 s >>
                                     checkArginfovr i >>
                                     checkSort0 sarg >>
                                     termToArg t >>=
                                     dropIndex n

  checkTarget : Type → Error ⊤
  checkTarget (el s (def f args)) with f ≟-Name self | drop (toℕ p) args
  checkTarget (el s (def f _)) | yes p | []    = checkSort0 s >> return tt
  checkTarget (el s (def f _)) | yes p | _ ∷ _ = fail "checkTarget: Indices in constructor target are not supported"
  checkTarget (el s (def f _)) | no ¬p | _     = fail "checkTarget: Invalid constructor target"
  checkTarget otherwise = fail "checkTarget: Invalid constructor target"

  termToConstructor′ : Error (List SafeArg)
  termToConstructor′ = let (pargs , ptarget) = takeArgs ct p in
                       let (args , target) = getArgs ptarget in
                       checkTarget target >>
                       sequenceM (zipStream (λ { n (s , a) → quoteArg n s a })
                                            (iterate suc 0) (toList args))

quoteConstructor : (self : Name)(c : Name) → Fin (suc (argCount (type c))) → Error SafeProduct
quoteConstructor self c p = _,_ c <$> termToConstructor self (type c) p

module TestTermToConstructor where
  el0 : Term → Type
  el0 = el (lit 0)

  argvr : ∀{A} → A → Arg A
  argvr = arg (arg-info visible relevant)

  data Dummy : Set where
    dZ : Dummy
    dS : Dummy → Dummy

  testZ : ok ((quote dZ) , []) ≡ quoteConstructor (quote Dummy) (quote dZ) (# 0)
  testZ = refl

  testS : ok ((quote dS) , Svar ∷ []) ≡ quoteConstructor (quote Dummy) (quote dS) (# 0)
  testS = refl

  data Dummy2 (A : Set) : Set where
    dRec : A → Dummy2 A

  testRec : ok (quote dRec , SK (var 0 []) ∷ []) ≡ quoteConstructor (quote Dummy2) (quote dRec) (# 1)
  testRec = refl

  data Dummy3 (A B : Set) : Set where
    dPair : A → B → Dummy3 A B
    dMulti : B → B → Dummy2 A → Dummy3 A B

  testPair : ok (quote dPair , SK (var 1 []) ∷
                               SK (var 0 []) ∷ [])
    ≡ quoteConstructor (quote Dummy3) (quote dPair) (# 2)
  testPair = refl

  -- type of dMulti : {A B : Set} → B → B → Dummy2 A → Dummy3 A B
  -- testMulti : ok (quote dMulti ,
  --                 SK (var 0 []) ∷
  --                 SK (var 0 []) ∷
  --                 SK (def (quote Dummy2) (argvr (var 1 []) ∷ [])) ∷ [])
  --             ≡ quoteConstructor (quote Dummy3) (quote dMulti) (# 2)
  -- testMulti = refl
