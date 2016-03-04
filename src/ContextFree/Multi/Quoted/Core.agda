module ContextFree.Multi.Quoted.Core where

open import Common
open import Builtin.Reflection
open import ContextFree.Multi.Params using (Param)

-- We do not want to use reflected Term's, because we can't unquote these in DescFunction.
-- We do want to allow some kinds of terms though..
-- Terms can be allowed if we can convert them to functions (Params → Set)
-- Terms with quoted names can not be converted! Unless... the quoted name can be represented
-- in our system.
-- Another option is to pass along a mapping from quoted names to (⋯ → Set)s, but that could
-- never be type safe

-- data SafeLiteral : Set where
--   nat : Nat → SafeLiteral

-- data SafeTerm : Nat → Set where
--   var : ∀{pc} → Fin pc → SafeTerm pc
--   def : ∀{pc} → Name → (p → Set) → SafeTerm pc
--   def : ∀{pc} → (sdt : NamedSafeDatatype) → paramsFor sdt → SafeTerm pc
--   lit : ∀{pc} → SafeLiteral → SafeTerm pc

-- Nat = def₀ (quote Nat)
-- Fin 3 = def (quote Fin) (argvr (lit (nat 3)))

data SafeArg {pc : Nat} : Set where
  Spar : Fin pc → SafeArg -- The type of the param is only stored in the Param List
  -- This can replace Spar:
  -- Sterm₀ : SafeTerm pc → SafeArg
  Srec : SafeArg

SafeProduct : {pc : Nat} → Set
SafeProduct {pc} = List (SafeArg {pc})

SafeSum : {pc : Nat} → Set
SafeSum {pc} = List (SafeProduct {pc})

record SafeDatatype : Set where
  constructor mk
  field pc : Nat
        params : Vec Param pc
        sop : SafeSum {pc}

SafeSumNames : {pc : Nat} → SafeSum {pc} → Set
SafeSumNames [] = ⊤
SafeSumNames (_ ∷ ps) = Name × SafeSumNames ps

SafeDatatypeNames : SafeDatatype → Set
SafeDatatypeNames (mk pc params sop) = Name × SafeSumNames sop



NamedSafeProduct : {pc : Nat} → Set
NamedSafeProduct {pc} = (Name × List (SafeArg {pc}))

NamedSafeSum : {pc : Nat} → Set
NamedSafeSum {pc} = List (NamedSafeProduct {pc})

record NamedSafeDatatype : Set where
  constructor mk
  field `dt : Name
        pc : Nat
        params : Vec Param pc
        sop : NamedSafeSum {pc}

private
  nameSafeSum : {pc : Nat} → (ss : SafeSum {pc}) → SafeSumNames ss → NamedSafeSum {pc}
  nameSafeSum [] tt = []
  nameSafeSum (p ∷ ps) (pn , psn) = (pn , p) ∷ nameSafeSum ps psn
  unnameSafeSum : {pc : Nat} → NamedSafeSum {pc} → Σ SafeSum SafeSumNames
  unnameSafeSum [] = [] , tt
  unnameSafeSum (p ∷ nps) = map× (_∷_ (snd p)) (_,_ (fst p)) (unnameSafeSum nps)

nameSafeDatatype : (sd : SafeDatatype) → SafeDatatypeNames sd → NamedSafeDatatype
nameSafeDatatype (mk pc params sop) (n , sopn) = mk n pc params (nameSafeSum sop sopn)

unnameSafeDatatype : NamedSafeDatatype → Σ SafeDatatype SafeDatatypeNames
unnameSafeDatatype (mk `dt pc params sopn) = map× (mk pc params) (_,_ `dt) (unnameSafeSum sopn)

private
  module Test where
    name-unname : ∀ x → uncurry nameSafeDatatype (unnameSafeDatatype x) ≡ x
    name-unname (mk `dt pc params sop) = cong (mk `dt pc params) (s sop)
      where
      s : ∀ x → uncurry nameSafeSum (unnameSafeSum x) ≡ x
      s [] = refl
      s ((_ , _) ∷ nps) = cong₂ _∷_ refl (s nps)

    private
      unname-name-sum : {pc : Nat} → ∀ ps psn → unnameSafeSum {pc} (nameSafeSum ps psn) ≡ (ps , psn)
      unname-name-sum [] tt = refl
      unname-name-sum (p ∷ ps) (pn , psn) rewrite unname-name-sum ps psn = refl

    unname-name : ∀ ps psn → unnameSafeDatatype (nameSafeDatatype ps psn) ≡ (ps , psn)
    unname-name (mk pc params sop) (n , sopn) rewrite unname-name-sum sop sopn = refl
