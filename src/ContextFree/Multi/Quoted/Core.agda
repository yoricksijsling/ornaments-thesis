module ContextFree.Multi.Quoted.Core where

open import Common
open import Builtin.Reflection
open import ContextFree.Multi.Params using (Param)

record Names (A : Set) : Set₁ where
  field
    Named : Set
    NamesFor : A → Set
    addNames : (x : A) → NamesFor x → Named
    removeNames : Named → Σ A NamesFor
    addRemoveNames : ∀ x → uncurry addNames (removeNames x) ≡ x
    removeAddNames : ∀ x y → removeNames (addNames x y) ≡ (x , y)

open Names {{...}} public

----------------------------------------
-- Args

data SafeArg {pc : Nat} : Set where
  Spar : Fin pc → SafeArg -- The type of the param is only stored in the Param List
  Srec : SafeArg
--  Srec : Vec Term ic → SafeArg

----------------------------------------
-- Products

SafeProduct : {pc : Nat} → Set
SafeProduct {pc} = List (SafeArg {pc})

instance
  safeProductNames : ∀ {pc} → Names (SafeProduct {pc})
  safeProductNames {pc} =
    record { Named = Name × List (SafeArg {pc}) ; NamesFor = λ _ → Name
           ; addNames = flip _,_ ; removeNames = λ { (nm , p) → p , nm}
           ; addRemoveNames = λ { (_ , _) → refl} ; removeAddNames = λ _ _ → refl
           }

----------------------------------------
-- Sums

SafeSum : {pc : Nat} → Set
SafeSum {pc} = List (SafeProduct {pc})

instance
  safeSumNames : ∀ {pc} → Names (SafeSum {pc})
  safeSumNames {pc} =
    record { Named = named ; NamesFor = namesFor
           ; addNames = add ; removeNames = remove
           ; addRemoveNames = addRemove ; removeAddNames = removeAdd
           }
    where
    named : Set
    named = List (Named {SafeProduct {pc}})
    namesFor : SafeSum → Set
    namesFor = foldr (λ p acc → NamesFor p × acc) ⊤
    add : (x : SafeSum) → namesFor x → named
    add [] tt = []
    add (p ∷ ps) (nm , nms) = addNames p nm ∷ add ps nms
    remove : named → Σ SafeSum namesFor
    remove [] = [] , tt
    remove ((nm , p) ∷ r) = map× (p ∷_) (nm ,_) (remove r)
    addRemove : ∀ x → uncurry add (remove x) ≡ x
    addRemove [] = refl
    addRemove ((_ , _) ∷ ps) = cong (_ ∷_) (addRemove ps)
    removeAdd : ∀ x y → remove (add x y) ≡ (x , y)
    removeAdd [] tt = refl
    removeAdd (_ ∷ ps) (_ , nms) rewrite removeAdd ps nms = refl

----------------------------------------
-- Datatype

record SafeDatatype : Set where
  constructor mk
  field {pc} : Nat
        params : Vec Param pc
        {ic} : Nat
        indices : Vec Param ic
        sop : SafeSum {pc}

record NamedSafeDatatype : Set where
  constructor mk
  field `dt : Name
        {pc} : Nat
        params : Vec Param pc
        {ic} : Nat
        indices : Vec Param ic
        sop : Named {SafeSum {pc}}

instance
  safeDatatypeNames : Names SafeDatatype
  safeDatatypeNames =
    record { Named = NamedSafeDatatype ; NamesFor = namesFor
           ; addNames = add ; removeNames = remove
           ; addRemoveNames = addRemove ; removeAddNames = removeAdd
           }
    where
    namesFor : SafeDatatype → Set
    namesFor (mk params indices sop) = NamesFor sop × Name
    add : (x : SafeDatatype) → namesFor x → NamedSafeDatatype
    add (mk params indices sop) (sopnms , nm) = mk nm params indices (addNames sop sopnms)
    remove : NamedSafeDatatype → Σ SafeDatatype namesFor
    remove (mk `dt params indices sop) = map× (mk params indices) (_, `dt) (removeNames sop)
    addRemove : ∀ x → uncurry add (remove x) ≡ x
    addRemove (mk `dt params indices sop) = cong (mk `dt params indices) (addRemoveNames {{safeSumNames}} sop)
    removeAdd : ∀ x y → remove (add x y) ≡ (x , y)
    removeAdd (mk params indices sop) (sopnms , nm) rewrite removeAddNames sop sopnms = refl
