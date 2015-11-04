module ContextFree.One.Quoting.Safe where

open import Data.List using (List; []; _∷_; map; [_]; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function
open import Reflection
open import ContextFree.One.Desc
open import TypeArgs
open import Stuff using (foldrWithDefault; mapFoldrWithDefault)

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
    params : List (Sort × Arg Type)
    sop : SafeSum


private
  argvr : ∀{A} → A → Arg A
  argvr = arg (arg-info visible relevant)

  ccon₀ : Name → Term
  ccon₀ n = con n []

  ccon₁ : Name → Term → Term
  ccon₁ n t = con n (argvr t ∷ [])

  ccon₂ : Name → Term → Term → Term
  ccon₂ n t₁ t₂ = con n (argvr t₁ ∷ argvr t₂ ∷ [])

  cvar₀ : ℕ → Term
  cvar₀ n = var n []

  cvar₁ : ℕ → Term → Term
  cvar₁ n t = var n (argvr t ∷ [])

  cclause₂ : Pattern → Pattern → Term → Clause
  cclause₂ p₁ p₂ t = clause (argvr p₁ ∷ argvr p₂ ∷ []) t

  cabsurd-clause₂ : Pattern → Pattern → Clause
  cabsurd-clause₂ p₁ p₂ = absurd-clause (argvr p₁ ∷ argvr p₂ ∷ [])

module ToDesc where
  ⟦_⟧arg : SafeArg → Term
  ⟦ SK S ⟧arg = ccon₁ (quote `K) S
  ⟦ Svar ⟧arg = ccon₀ (quote `var)

  ⟦_⟧product : SafeProduct → Term
  ⟦_⟧product = foldrWithDefault (ccon₀ (quote `1))
                                (ccon₂ (quote _`*_)) ∘′ map ⟦_⟧arg 

  ⟦_⟧sum : SafeSum → Term
  ⟦_⟧sum = (foldrWithDefault (ccon₀ (quote `0))
                             (ccon₂ (quote _`+_))) ∘′ (map ⟦_⟧product)

  ⟦_⟧datatype : SafeDatatype → Term
  ⟦ mk params sop ⟧datatype = addArgsTm params ⟦ sop ⟧sum
