module ContextFree.One.Quoting where

open import Data.Error using (Error; ok; fail; fromMaybe; isOk?; fromOk)
open import Data.String
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Product
open import Data.List using (List; []; _∷_; map)
open import Data.Unit
open import Function
open import Level renaming (zero to lzero; suc to lsuc)
open import Reflection
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (True)

open import ContextFree.One.Desc

open Data.Error.Monad

foldrWithDefault : ∀ {a} {A : Set a} → A → (A → A → A) → List A → A
foldrWithDefault d f [] = d
foldrWithDefault d f (x ∷ []) = x
foldrWithDefault d f (x ∷ y ∷ ys) = f x (foldrWithDefault d f (y ∷ ys))

getDatatype : Name → Error Data-type
getDatatype n = fromMaybe (showName n ++ " is not a data type")
                          (def2dt (definition n))
  where
  def2dt : Definition → Maybe Data-type
  def2dt (function _) = nothing
  def2dt (data-type x) = just x
  def2dt (record′ _) = nothing
  def2dt constructor′ = nothing
  def2dt axiom = nothing
  def2dt primitive′ = nothing

getConstructors : Data-type → Error (List Name)
getConstructors dt = ok (constructors dt)

checkSort0 : Sort → Error ⊤
checkSort0 (lit zero) = ok tt
checkSort0 _ = fail "Sort is not `lit 0`"

checkArginfovr : Arg-info → Error ⊤
checkArginfovr (arg-info visible relevant) = ok tt
checkArginfovr (arg-info _ _) = fail "Arg is not visible and relevant"

extractArgs : Type → Error (List (Sort × Arg Type) × Type)
extractArgs (el s (pi argt t₂)) = extractArgs t₂ >>= λ { (args , target) →
                                  return ((s , argt) ∷ args , target) }
extractArgs t = return ([] , t)

constructorDesc : Name → Type → Error Desc
constructorDesc self = constructorDesc′
  where
  argTermDesc : Term → Error Desc
  argTermDesc (def f args) with f ≟-Name self
  argTermDesc (def f [])      | yes p = return `var
  argTermDesc (def f (_ ∷ _)) | yes p = fail "argTermDesc: self-reference has arguments"
  argTermDesc (def f args)    | no ¬p = fail "argTermDesc: Invalid argument in constructor"
  argTermDesc otherwise = fail "argTermDesc: Invalid argument in constructor"

  argDesc : Sort → Arg Type → Error Desc
  argDesc s (arg i (el sarg t)) = checkSort0 s >>
                                  checkArginfovr i >>
                                  checkSort0 sarg >>
                                  argTermDesc t

  checkTarget : Type → Error ⊤
  checkTarget (el s (def f args)) with f ≟-Name self
  checkTarget (el s (def f []))      | yes p = checkSort0 s >> return tt
  checkTarget (el s (def f (_ ∷ _))) | yes p = fail "checkTarget: Indices in constructor target are not supported"
  checkTarget (el s (def f args))    | no ¬p = fail "checkTarget: Invalid constructor target"
  checkTarget otherwise = fail "checkTarget: Invalid constructor target"

  constructorDesc′ : Type → Error Desc
  constructorDesc′ t = extractArgs t >>= λ { (args , target) →
                       checkTarget target >>
                       (mapM (uncurry′ argDesc) args) >>=
                       return ∘′ foldrWithDefault `1 _`*_ }


module TestConstructorToDesc where
  argvr : ∀{A : Set} → A → Arg A
  argvr = arg (arg-info visible relevant)

  el0 : Term → Type
  el0 = el (lit 0)

  data Dummy : Set where

  -- Dummy
  testZero : ok `1 ≡ constructorDesc (quote Dummy)
    (el0 (def (quote Dummy) []))
  testZero = refl

  -- Dummy → Dummy
  testSuc : ok `var ≡ constructorDesc (quote Dummy)
    (el0 (pi (argvr (el0 (def (quote Dummy) [])))
             (el0 (def (quote Dummy) []))))
  testSuc = refl

  data List' (A : Set) : Set where
    nil : List' A
    cons : A → List' A → List' A

  -- testNil : {!!}
  -- testNil = {!!}

quoteDesc : Name → Error Desc
quoteDesc n = getDatatype n >>=
              getConstructors >>=
              mapM (constructorDesc n ∘′ type) >>=
              return ∘′ foldrWithDefault `0 _`+_

quoteDesc! : (n : Name){isOk : True (isOk? (quoteDesc n))} → Desc
quoteDesc! n {isOk} = fromOk (quoteDesc n) {isOk}

