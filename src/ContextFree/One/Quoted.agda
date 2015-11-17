module ContextFree.One.Quoted where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; Σ) renaming (map to map×)
open import Data.Unit.Base
open import Data.Vec using (Vec)
open import Reflection using (Name)
open import ContextFree.One.Params using (Param)

-- We do not want to use reflected Term's, because we can't unquote these in DescFunction.
-- We do want to allow some kinds of terms though..
-- Terms can be allowed if we can convert them to functions (Params → Set)
-- Terms with quoted names can not be converted! Unless... the qouted name can be represented
-- in our system.
-- Another option is to pass along a mapping from quoted names to (⋯ → Set)s, but that could
-- never be type safe

-- data SafeLiteral : Set where
--   nat : ℕ → SafeLiteral

-- data SafeTerm : ℕ → Set where
--   var : ∀{pc} → Fin pc → SafeTerm pc
--   def : 
--   lit : ∀{pc} → SafeLiteral → SafeTerm pc

-- ℕ = def₀ (quote ℕ)
-- Fin 3 = def (quote Fin) (argvr (lit (nat 3)))

data SafeArg {pc : ℕ} : Set where
  Spar : Fin pc → SafeArg -- The type of the param is only stored in the Param List
  -- This can replace Spar:
  --   Sterm₀ : SafeTerm pc → SafeArg
  Srec : SafeArg

SafeProduct : {pc : ℕ} → Set
SafeProduct {pc} = List (SafeArg {pc})

SafeSum : {pc : ℕ} → Set
SafeSum {pc} = List (SafeProduct {pc})

record SafeDatatype : Set where
  constructor mk
  field
    pc : ℕ
    params : Vec Param pc
    sop : SafeSum {pc}


SafeSumNames : {pc : ℕ} → SafeSum {pc} → Set
SafeSumNames [] = ⊤
SafeSumNames (_ ∷ ps) = Name × SafeSumNames ps

SafeDatatypeNames : SafeDatatype → Set
SafeDatatypeNames (mk pc params sop) = Name × SafeSumNames sop



NamedSafeProduct : {pc : ℕ} → Set
NamedSafeProduct {pc} = (Name × List (SafeArg {pc}))

NamedSafeSum : {pc : ℕ} → Set
NamedSafeSum {pc} = List (NamedSafeProduct {pc})

record NamedSafeDatatype : Set where
  constructor mk
  field
    dtname : Name
    pc : ℕ
    params : Vec Param pc
    sop : NamedSafeSum {pc}

private
  nameSafeSum : {pc : ℕ} → (ss : SafeSum {pc}) → SafeSumNames ss → NamedSafeSum {pc}
  nameSafeSum [] tt = []
  nameSafeSum (p ∷ ps) (pn , psn) = (pn , p) ∷ nameSafeSum ps psn
  unnameSafeSum : {pc : ℕ} → NamedSafeSum {pc} → Σ SafeSum SafeSumNames
  unnameSafeSum [] = [] , tt
  unnameSafeSum ((pn , p) ∷ nps) = map× (_∷_ p) (_,_ pn) (unnameSafeSum nps)

nameSafeDatatype : (sd : SafeDatatype) → SafeDatatypeNames sd → NamedSafeDatatype
nameSafeDatatype (mk pc params sop) (n , sopn) = mk n pc params (nameSafeSum sop sopn)

unnameSafeDatatype : NamedSafeDatatype → Σ SafeDatatype SafeDatatypeNames
unnameSafeDatatype (mk dtname pc params sopn) = map× (mk pc params) (_,_ dtname) (unnameSafeSum sopn)

module _ where
  open import Data.Product using (uncurry)
  open import Relation.Binary.PropositionalEquality

  name-unname : ∀ x → uncurry nameSafeDatatype (unnameSafeDatatype x) ≡ x
  name-unname (mk dtname pc params sop) = cong (mk dtname pc params) (sum sop)
    where
    sum : ∀ x → uncurry nameSafeSum (unnameSafeSum x) ≡ x
    sum [] = refl
    sum (_ ∷ nps) = cong₂ _∷_ refl (sum nps)

  private
    unname-name-sum : {pc : ℕ} → ∀ ps psn → unnameSafeSum {pc} (nameSafeSum ps psn) ≡ ps , psn
    unname-name-sum [] tt = refl
    unname-name-sum (p ∷ ps) (pn , psn) rewrite unname-name-sum ps psn = refl

  unname-name : ∀ ps psn → unnameSafeDatatype (nameSafeDatatype ps psn) ≡ ps , psn
  unname-name (mk pc params sop) (n , sopn) rewrite unname-name-sum sop sopn = refl
