module ContextFree.Multi.Quoted.ToDesc where

open import Common
open import Builtin.Reflection using (visible)
open import ContextFree.Multi.Desc
open import ContextFree.Multi.Params
open import ContextFree.Multi.Quoted.Core
open import Stuff using (finReverse)

module SD = SafeDatatype

SafeDatatypeToDesc : (sdt : SafeDatatype) → Set₁
SafeDatatypeToDesc (mk {pc} _ _ _) = IODesc (Fin pc) ⊤

safeDatatypeToDesc : (sdt : SafeDatatype) → SafeDatatypeToDesc sdt
safeDatatypeToDesc (mk {pc} params indices sop) = `fix (sumDesc sop)
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

private
  module Test where
    treeSdt : SafeDatatype
    treeSdt = mk (param₀ visible "" ∷ [])
                 []
                 ([] ∷
                 (Spar zero ∷ Srec ∷ []) ∷
                 (Spar zero ∷ Srec ∷ Srec ∷ []) ∷ [])


    treeDesc : IODesc (Fin 1) ⊤
    treeDesc = safeDatatypeToDesc treeSdt

    testTreeDesc : safeDatatypeToDesc treeSdt
                 ≡ (`fix $ `1 `+
                           `var (left 0) `* `var (right tt) `* `1 `+
                           `var (left 0) `* `var (right tt) `* `var (right tt) `* `1 `+
                           `0)
    testTreeDesc = refl

    pairSdt : SafeDatatype
    pairSdt = mk (param₀ visible "" ∷ param₀ visible "" ∷ [])
                 []
                 ((Spar 1 ∷ Spar 0 ∷ []) ∷ [])

    testPairDesc : safeDatatypeToDesc pairSdt
                 ≡ (`fix $ `var (left 0) `* `var (left 1) `* `1 `+
                           `0)
    testPairDesc = refl
