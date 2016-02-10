module ContextFree.One.DescFunction where

open import Common
open import Builtin.Reflection
open import ContextFree.One.Desc
open import ContextFree.One.Params
open import ContextFree.One.Quoted
open import Stuff using (finReverse)

module SD = SafeDatatype

private
  ParamTy : Param → Set₁
  ParamTy (param₀ v _) = Set
  
  ParamTup : {pc : Nat} → Vec Param pc → Set₁
  ParamTup [] = ⊤′
  ParamTup (p ∷ ps) = ParamTy p × ParamTup ps
  
  lookupParam : {pc : Nat}{params : Vec Param pc} → Fin pc → ParamTup params → Σ Param ParamTy
  lookupParam k ptup = lookupParam′ (finReverse k) ptup
    where
    lookupParam′ : {pc : Nat}{params : Vec Param pc} → Fin pc → ParamTup params → Σ Param ParamTy
    lookupParam′ {params = _ ∷ _} zero (pv , _) = _ , pv
    lookupParam′ {params = _ ∷ _} (suc k) (_ , ptup) = lookupParam′ k ptup
  
  descFun× : (sdt : SafeDatatype) → ParamTup (SD.params sdt) → Desc
  descFun× (mk pc params sop) ptup = foldr (_`+_ ∘ productDesc) `0 sop
    where
    argDesc : SafeArg {pc} → Desc
    argDesc (Spar i) with lookupParam i ptup
    argDesc (Spar i) | param₀ v _ , p = `P₀ p
    argDesc Srec = `var
    productDesc : SafeProduct → Desc
    productDesc = foldr (_`*_ ∘ argDesc) `1

  DescFun′ : {pc : Nat} → Vec Param pc → Set₁
  DescFun′ [] = Desc
  DescFun′ (param₀ visible _ ∷ ps) = Set → DescFun′ ps
  DescFun′ (param₀ hidden _ ∷ ps) = {s : Set} → DescFun′ ps
  DescFun′ (param₀ instance′ _ ∷ ps) = {{s : Set}} → DescFun′ ps
  
  toDescFun′ : ∀ {pc}{ps : Vec Param pc} → (ParamTup ps → Desc) → DescFun′ ps
  toDescFun′ {ps = []} f = f tt
  toDescFun′ {ps = param₀ visible _ ∷ ps} f = λ v → toDescFun′ (curry f v)
  toDescFun′ {ps = param₀ hidden _ ∷ ps} f = λ {v} → toDescFun′ (curry f v)
  -- Instance arguments don't really make sense here
  toDescFun′ {ps = param₀ instance′ _ ∷ ps} f = λ {{v}} → toDescFun′ (curry f v)

DescFun : (sdt : SafeDatatype) → Set₁
DescFun (mk pc params sop) = DescFun′ params

descFun : (sdt : SafeDatatype) → DescFun sdt
descFun sdt = toDescFun′ (descFun× sdt)

module _ where
  treeSdt : SafeDatatype
  treeSdt = mk 1 (param₀ visible "" ∷ [])
                 ([] ∷
                 (Spar zero ∷ Srec ∷ []) ∷
                 (Spar zero ∷ Srec ∷ Srec ∷ []) ∷ [])


  treeDesc : Set → Desc
  treeDesc A = descFun treeSdt A

  testTreeDesc : ∀ A → descFun treeSdt A
               ≡ (`1 `+ `P₀ A `* `var `* `1 `+ `P₀ A `* `var `* `var `* `1 `+ `0)
  testTreeDesc A = refl
