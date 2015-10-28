module ContextFree.One.Quoting where

open import Data.Error using (Error; ok; fail; fromMaybe; isOk?; fromOk)
open import Data.String
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing; maybe)
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

constructorToDesc : Name → Type → Error Desc
constructorToDesc self = constructorToDesc′
  where
  argterm : Term → Error Desc
  argterm (def f args) with f ≟-Name self
  argterm (def .self []) | yes refl = ok `var
  argterm (def .self (_ ∷ _)) | yes refl = fail "Constructor argument: self-reference has arguments"
  argterm (def f args) | no _ = fail "Invalid constructor argument"

  argterm (var x args) = fail "Invalid constructor argument"
  argterm (con c args) = fail "Invalid constructor argument"
  argterm (lam v t) = fail "Invalid constructor argument"
  argterm (pat-lam cs args) = fail "Invalid constructor argument"
  argterm (pi t₁ t₂) = fail "Invalid constructor argument"
  argterm (sort x) = fail "Invalid constructor argument"
  argterm (lit x) = fail "Invalid constructor argument"
  argterm unknown = fail "Invalid constructor argument"

  mutual
    term : Term → Error Desc
    term (def f args) with f ≟-Name self
    term (def .self []) | yes refl = ok `1
    term (def .self (_ ∷ _)) | yes refl = fail "Constructor target has arguments"
    term (def f args) | no _ = fail "Constructor target is not self"
    term (pi (arg i (el s t)) rest) = checkArginfovr i >>
                                      checkSort0 s >>
                                      argterm t >>= λ argdesc →
                                      constructorToDesc′ rest >>= λ restdesc →
                                      return (argdesc `* restdesc)
    term (lam v t₁) = fail "Constructor term is `lam v t`"
    term (pat-lam cs args) = fail "Constructor term is `pat-lam cs args`"
    term (var x args) = fail "Constructor term is `var x args`"
    term (con c args) = fail "Constructor term is `con c args`"
    term (sort x) = fail "Constructor term is `sort x`"
    term (lit x) = fail "Constructor term is `lit x`"
    term unknown = fail "Constructor term is `unknown`"

    constructorToDesc′ : Type → Error Desc
    constructorToDesc′ (el s t) = checkSort0 s >> term t


module TestConstructorToDesc where
  argvr : ∀{A : Set} → A → Arg A
  argvr = arg (arg-info visible relevant)

  el0 : Term → Type
  el0 = el (lit 0)

  data Dummy : Set where

  -- Dummy
  testZero : ok `1 ≡ constructorToDesc (quote Dummy)
    (el0 (def (quote Dummy) []))
  testZero = refl

  -- Dummy → Dummy
  testSuc : ok (`var `* `1) ≡ constructorToDesc (quote Dummy)
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
              mapM (constructorToDesc n ∘′ type) >>=
              return ∘′ foldrWithDefault `0 _`+_

quoteDesc! : (n : Name){isOk : True (isOk? (quoteDesc n))} → Desc
quoteDesc! n {isOk} = fromOk (quoteDesc n) {isOk}

