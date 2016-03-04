module ContextFree.Multi.DescFunction where

open import Common
open import Builtin.Reflection using (visible)
open import ContextFree.Multi.Desc
open import ContextFree.Multi.Params
open import ContextFree.Multi.Quoted
open import Stuff using (finReverse)

module SD = SafeDatatype

DescFun : (sdt : SafeDatatype) → Set₁
DescFun (mk pc _ _) = IODesc (Either (Fin pc) ⊤) ⊤

descFun : (sdt : SafeDatatype) → DescFun sdt
descFun (mk pc params sop) = sumDesc sop
  where
  argDesc : SafeArg → IODesc (Either (Fin pc) ⊤) ⊤
  argDesc (Spar i) = `var (left (finReverse i))
  argDesc Srec = `var (right tt)
  productDesc : List SafeArg → IODesc (Either (Fin pc) ⊤) ⊤
  productDesc [] = `1
  productDesc (a ∷ as) = argDesc a `* productDesc as
  sumDesc : List SafeProduct → IODesc (Either (Fin pc) ⊤) ⊤
  sumDesc [] = `0
  sumDesc (p ∷ ps) = productDesc p `+ sumDesc ps

module _ where
  treeSdt : SafeDatatype
  treeSdt = mk 1 (param₀ visible "" ∷ [])
                 ([] ∷
                 (Spar zero ∷ Srec ∷ []) ∷
                 (Spar zero ∷ Srec ∷ Srec ∷ []) ∷ [])


  treeDesc : IODesc (Either (Fin 1) ⊤) ⊤
  treeDesc = descFun treeSdt

  testTreeDesc : descFun treeSdt
               ≡ (`1 `+ `var (left 0) `* `var (right tt) `* `1 `+ `var (left 0) `* `var (right tt) `* `var (right tt) `* `1 `+ `0)
  testTreeDesc = refl

  pairSdt : SafeDatatype
  pairSdt = mk 2 (param₀ visible "" ∷ param₀ visible "" ∷ [])
                 ((Spar 1 ∷ Spar 0 ∷ []) ∷ [])

  testPairDesc : descFun pairSdt
               ≡ (`var (left 0) `* `var (left 1) `* `1 `+ `0)
  testPairDesc = refl
