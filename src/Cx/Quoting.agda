
module Cx.Quoting where

open import Tactic.Reflection
open import Container.Traversable

open import Reflection
open import Common
open import Cx.Named
open import Cx.Quoting.Constructor
open import Cx.Quoting.Cx
open import Cx.Quoting.QuotedDesc public

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
  =| I ← typeToCx #p nothing dttype
  =| Γ ← typeToCx 0 (just #p) dttype
  =| `cnames ← getConstructors `dt
  =| datdesc ← quoteConstructors `dt #p I Γ `cnames
  =| return (mk `dt (listToVec `cnames) datdesc)

macro
  quoteDatatypeᵐ : (`dt : Name) → Tactic
  quoteDatatypeᵐ `dt = evalTC (quoteDatatype `dt)
