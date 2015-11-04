module ContextFree.One.Quoting where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; toℕ; #_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_; s≤s)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Product using (_×_; _,_; uncurry′; ∃; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map; length; drop)
open import Data.List.All using (all)
open import Data.Vec using (Vec; []; _∷_)
open import Data.String
open import Data.Unit using (⊤; tt)
open import Function
open import Reflection
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True)

open import ContextFree.One.Desc
open import Data.Error
open Data.Error.Monad
open import TypeArgs
open import Stuff

argvr : ∀{A : Set} → A → Arg A
argvr = arg (arg-info visible relevant)

data QDesc : Set where
  QK : (S : Term) → QDesc
  Q0 : QDesc
  Q1 : QDesc
  _Q+_ : (A B : QDesc) → QDesc
  _Q*_ : (A B : QDesc) → QDesc
  Qvar : QDesc

QDescP : Set
QDescP = List (Sort × Arg Type) × QDesc

⟦_⟧QDesc : QDesc → Term
⟦ QK S ⟧QDesc = con (quote `K) (argvr S ∷ [])
⟦ Q0 ⟧QDesc = con (quote `0) []
⟦ Q1 ⟧QDesc = con (quote `1) []
⟦ A Q+ B ⟧QDesc = con (quote _`+_) (argvr ⟦ A ⟧QDesc ∷ argvr ⟦ B ⟧QDesc ∷ [])
⟦ A Q* B ⟧QDesc = con (quote _`*_) (argvr ⟦ A ⟧QDesc ∷ argvr ⟦ B ⟧QDesc ∷ [])
⟦ Qvar ⟧QDesc = con (quote `var) []

⟦_⟧QDescP : QDescP → Term
⟦ ps , d ⟧QDescP = addArgsTm ps ⟦ d ⟧QDesc

--------------------

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
checkSort0 s = log "Sort is not `lit 0`" >> fail s

checkArginfovr : Arg-info → Error ⊤
checkArginfovr (arg-info visible relevant) = ok tt
checkArginfovr (arg-info _ _) = fail "Arg is not visible and relevant"

constructorDesc : Name → (t : Type) → Fin (suc (argCount t)) → Error QDesc
constructorDesc self ct p = constructorDesc′
  where
  argTermDesc : Term → Error QDesc
  argTermDesc (def f args) with f ≟-Name self | drop (toℕ p) args -- drop p args
  argTermDesc (def f args) | yes p | []    = return Qvar
  argTermDesc (def f args) | yes p | _ ∷ _ = fail "argTermDesc: self-reference has arguments"
  argTermDesc (def f args) | no ¬p | _     = log "argTermDesc: Invalid argument in constructor" >>
                                             fail (def f args)
  argTermDesc (var x args) = return (QK (var x args)) -- TODO: Check that the debruijn index does not change
  argTermDesc (sort s) = return (QK (sort s))
  argTermDesc otherwise = log "argTermDesc: Invalid argument in constructor" >> fail otherwise

  argDesc : Sort → Arg Type → Error QDesc
  argDesc s (arg i (el sarg t)) = -- checkSort0 s >>
                                  checkArginfovr i >>
                                  -- checkSort0 sarg >>
                                  argTermDesc t

  checkTarget : Type → Error ⊤
  checkTarget (el s (def f args)) with f ≟-Name self | drop (toℕ p) args
  checkTarget (el s (def f _)) | yes p | []    = -- checkSort0 s >>
                                                 return tt
  checkTarget (el s (def f _)) | yes p | _ ∷ _ = fail "checkTarget: Indices in constructor target are not supported"
  checkTarget (el s (def f _)) | no ¬p | _     = fail "checkTarget: Invalid constructor target"
  checkTarget otherwise = fail "checkTarget: Invalid constructor target"

  constructorDesc′ : Error QDesc
  constructorDesc′ = let (pargs , ptarget) = takeArgs ct p in
                     let (args , target) = getArgs ptarget in
                     checkTarget target >>
                     (mapM (uncurry′ argDesc) (Data.Vec.toList args)) >>=
                     return ∘′ foldrWithDefault Q1 _Q*_


module TestConstructorToDesc where
  el0 : Term → Type
  el0 = el (lit 0)

  data Dummy : Set where

  -- Dummy
  testZero : ok Q1 ≡ constructorDesc (quote Dummy)
    (el0 (def (quote Dummy) []))
    (# 0)
  testZero = refl

  -- Dummy → Dummy
  testSuc : ok Qvar ≡ constructorDesc (quote Dummy)
    (el0 (pi (argvr (el0 (def (quote Dummy) [])))
             (el0 (def (quote Dummy) []))))
    (# 0)
  testSuc = refl

Params : Set
Params = ℕ

_fits_ : Params → Name → Set
_fits_ p n = p ≤ argCount (type n)

_fits?_ : ∀ p n → Dec (p fits n)
p fits? n = p ≤? argCount (type n)

quoteQDesc : (n : Name) (p : ℕ) →
  Error QDescP
quoteQDesc n p =
  getDatatype n >>= λ dt →
  getConstructors dt >>= λ cs →
  decToError "Too many params for datatype" (p ≤? argCount (type n)) >>= λ pfitsn →
  let params = proj₁ (takeArgs (type n) (Data.Fin.fromℕ≤ (s≤s pfitsn))) in
  -- TODO: extract params and check that constructors fit exactly
  decToError "Too many params for some constructors" (all (_fits?_ p) cs) >>= λ pfitscs →
  sequenceM (mapAllToList (λ {c} pfitsc → constructorDesc n (type c) (Data.Fin.fromℕ≤ (s≤s pfitsc)))
                          pfitscs) >>= λ cdescs →
  return (Data.Vec.toList params , (foldrWithDefault Q0 _Q+_ cdescs))

quoteDesc : Name → ℕ → Error Term
quoteDesc n p = quoteQDesc n p >>= return ∘′ ⟦_⟧QDescP

quoteDesc! : (n : Name)(p : ℕ){isOk : True (isOk? (quoteDesc n p))} → Term
quoteDesc! n p {isOk} = fromOk isOk

