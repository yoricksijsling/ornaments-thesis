module ContextFree.One.DescFunction where

open import ContextFree.One.Desc
open import ContextFree.One.Params
open import ContextFree.One.Quoted
open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Properties as FinProps
open import Data.List using (foldr)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; ,_; curry)
open import Data.Unit
open import Data.Vec using (Vec; []; _∷_)
open import Function
open import Level using (Lift; lift)
open import Reflection

module SD = SafeDatatype

private
  ParamTy : Param → Set₁
  ParamTy (param₀ v) = Set
  
  ParamTup : {pc : ℕ} → Vec Param pc → Set₁
  ParamTup [] = Lift ⊤
  ParamTup (p ∷ ps) = ParamTy p × ParamTup ps
  
  lookupParam : {pc : ℕ}{params : Vec Param pc} → Fin pc → ParamTup params → Σ Param ParamTy
  lookupParam k ptup = lookupParam′ (FinProps.reverse k) ptup
    where
    lookupParam′ : {pc : ℕ}{params : Vec Param pc} → Fin pc → ParamTup params → Σ Param ParamTy
    lookupParam′ {params = _ ∷ _} zero (pv , _) = , pv
    lookupParam′ {params = _ ∷ _} (suc k) (_ , ptup) = lookupParam′ k ptup
  
  descFun× : (sdt : SafeDatatype) → ParamTup (SD.params sdt) → Desc
  descFun× (mk pc params sop) ptup = foldr (_`+_ ∘′ productDesc) `0 sop
    where
    argDesc : SafeArg {pc} → Desc
    argDesc (Spar i) with lookupParam i ptup
    argDesc (Spar i) | param₀ v , p = `P₀ p
    argDesc Svar = `var
    productDesc : SafeProduct → Desc
    productDesc = foldr (_`*_ ∘′ argDesc) `1

  DescFun′ : {pc : ℕ} → Vec Param pc → Set₁
  DescFun′ [] = Desc
  DescFun′ (param₀ visible ∷ ps) = Set → DescFun′ ps
  DescFun′ (param₀ hidden ∷ ps) = {s : Set} → DescFun′ ps
  DescFun′ (param₀ instance′ ∷ ps) = {{s : Set}} → DescFun′ ps
  
  toDescFun′ : ∀ {pc}{ps : Vec Param pc} → (ParamTup ps → Desc) → DescFun′ ps
  toDescFun′ {ps = []} f = f (lift tt)
  toDescFun′ {ps = param₀ visible ∷ ps} f = λ v → toDescFun′ (curry f v)
  toDescFun′ {ps = param₀ hidden ∷ ps} f = λ {v} → toDescFun′ (curry f v)
  toDescFun′ {ps = param₀ instance′ ∷ ps} f = λ {{v}} → toDescFun′ (curry f v)

DescFun : (sdt : SafeDatatype) → Set₁
DescFun (mk pc params sop) = DescFun′ params

descFun : (sdt : SafeDatatype) → DescFun sdt
descFun sdt = toDescFun′ (descFun× sdt)
