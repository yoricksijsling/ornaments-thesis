module ContextFree.One.Quoted where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; Σ) renaming (map to map×)
open import Data.Unit
open import Reflection

Params : Set
Params = List (Sort × Arg Type)


data SafeArg : Set where
  SK : (S : Term) → SafeArg
  Svar : SafeArg

SafeProduct : Set
SafeProduct = List SafeArg

SafeSum : Set
SafeSum = List SafeProduct

record SafeDatatype : Set where
  constructor mk
  field
    params : Params
    sop : SafeSum


SafeSumNames : SafeSum → Set
SafeSumNames [] = ⊤
SafeSumNames (_ ∷ ps) = Name × SafeSumNames ps

SafeDatatypeNames : SafeDatatype → Set
SafeDatatypeNames (mk params sop) = Name × SafeSumNames sop



NamedSafeProduct : Set
NamedSafeProduct = (Name × List SafeArg)

NamedSafeSum : Set
NamedSafeSum = List NamedSafeProduct

record NamedSafeDatatype : Set where
  constructor mk
  field
    dtname : Name
    params : Params
    sop : NamedSafeSum



private
  nameSafeSum : (ss : SafeSum) → SafeSumNames ss → NamedSafeSum
  nameSafeSum [] tt = []
  nameSafeSum (p ∷ ps) (pn , psn) = (pn , p) ∷ nameSafeSum ps psn
  unnameSafeSum : NamedSafeSum → Σ SafeSum SafeSumNames
  unnameSafeSum [] = [] , tt
  unnameSafeSum ((pn , p) ∷ nps) = map× (_∷_ p) (_,_ pn) (unnameSafeSum nps)

nameSafeDatatype : (sd : SafeDatatype) → SafeDatatypeNames sd → NamedSafeDatatype
nameSafeDatatype (mk params sop) (n , sopn) = mk n params (nameSafeSum sop sopn)

unnameSafeDatatype : NamedSafeDatatype → Σ SafeDatatype SafeDatatypeNames
unnameSafeDatatype (mk dtname params sopn) = map× (mk params) (_,_ dtname) (unnameSafeSum sopn)

module Iso where
  open import Data.Product using (uncurry)
  open import Relation.Binary.PropositionalEquality

  name-unname : ∀ x → uncurry nameSafeDatatype (unnameSafeDatatype x) ≡ x
  name-unname (mk dtname params sop) = cong (mk dtname params) (sum sop)
    where
    sum : ∀ x → uncurry nameSafeSum (unnameSafeSum x) ≡ x
    sum [] = refl
    sum (_ ∷ nps) = cong₂ _∷_ refl (sum nps)

  private
    unname-name-sum : ∀ ps psn → unnameSafeSum (nameSafeSum ps psn) ≡ ps , psn
    unname-name-sum [] tt = refl
    unname-name-sum (p ∷ ps) (pn , psn) rewrite unname-name-sum ps psn = refl

  unname-name : ∀ ps psn → unnameSafeDatatype (nameSafeDatatype ps psn) ≡ ps , psn
  unname-name (mk params sop) (n , sopn) rewrite unname-name-sum sop sopn = refl
