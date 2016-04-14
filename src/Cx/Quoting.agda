
module Cx.Quoting where

open import Tactic.Reflection
open import Container.Traversable

open import Reflection
open import Common
open import Cx.Named
open import Cx.Quoting.Constructor
open import Cx.Quoting.Cx
open import Cx.Quoting.Indices

record SomeDatDesc : Set₂ where
  constructor mk
  field
    {I} : Set
    {Γ} : Cx
    {#c} : Nat
    desc : DatDesc I Γ #c


private
  beforeDot′ : List Char → List Char
  beforeDot′ [] = []
  beforeDot′ (c ∷ cs) = if eqChar c '.'
                        then []
                          else c ∷ beforeDot′ cs
-- Very elegant way of getting everything after the last dot.
cnameString : Name → String
cnameString = packString ∘ reverse ∘ beforeDot′ ∘ reverse ∘ unpackString ∘ show
private
  test-cnameString : cnameString (quote SomeDatDesc) ≡ "SomeDatDesc"
  test-cnameString = refl

quoteConstructors : (`dt : Name) (#p : Nat) → ∀ I Γ → (cnames : List Name) → TC (DatDesc I Γ (length cnames))
quoteConstructors `dt #p I Γ [] = return `0
quoteConstructors `dt #p I Γ (cname ∷ cnames) =
  do c ← quoteConstructor `dt #p I Γ cname
  -| cs ← quoteConstructors `dt #p I Γ cnames
  -| return (cnameString cname ∣ c ⊕ cs)

quoteDatatype : (`dt : Name) → TC SomeDatDesc
quoteDatatype `dt =
  do dttype ← getType `dt
  =| #p ← getParameters `dt
  =| I ← getIndices #p dttype
  =| Γ ← paramCx #p dttype
  =| cnames ← getConstructors `dt
  =| datdesc ← quoteConstructors `dt #p I Γ cnames
  =| return (mk datdesc)

macro
  quoteDatatypeᵐ : (`dt : Name) → Tactic
  quoteDatatypeᵐ `dt = evalTC (quoteDatatype `dt)
