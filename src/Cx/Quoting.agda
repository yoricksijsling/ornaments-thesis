
module Cx.Quoting where

open import Tactic.Reflection
open import Container.Traversable

open import Reflection
open import Common
open import Cx.Named
open import Cx.Quoting.Constructor
open import Cx.Quoting.Cx
open import Cx.Quoting.Indices

record QuotedDesc : Set₂ where
  constructor mk
  field
    {I} : Set
    {Γ} : Cx
    {#c} : Nat
    `datatypeName : Name
    `constructorNames : Vec Name #c
    desc : DatDesc I Γ #c

quoteConstructors : (`dt : Name) (#p : Nat) → ∀ I Γ → (cnames : List Name) → TC (DatDesc I Γ (length cnames))
quoteConstructors `dt #p I Γ [] = return `0
quoteConstructors `dt #p I Γ (cname ∷ cnames) =
  do c ← quoteConstructor `dt #p I Γ cname
  -| cs ← quoteConstructors `dt #p I Γ cnames
  -| return (c ⊕ cs)

quoteDatatype : (`dt : Name) → TC QuotedDesc
quoteDatatype `dt =
  do dttype ← getType `dt
  =| #p ← getParameters `dt
  =| I ← getIndices #p dttype
  =| Γ ← paramCx #p dttype
  =| `cnames ← getConstructors `dt
  =| datdesc ← quoteConstructors `dt #p I Γ `cnames
  =| return (mk `dt (listToVec `cnames) datdesc)

macro
  quoteDatatypeᵐ : (`dt : Name) → Tactic
  quoteDatatypeᵐ `dt = evalTC (quoteDatatype `dt)
