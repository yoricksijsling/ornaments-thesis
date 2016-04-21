
module Cx.HasDesc.Core where

open import Common
open import Reflection

open import Cx.Named
open import Cx.Quoting.QuotedDesc public

record HasDesc (A : Set) : Set₂ where
  constructor mk
  field
    {I} : Cx
    {Γ} : Cx
    {#c} : Nat
    `datatypeName : Name
    `constructorNames : Vec Name #c
    desc : DatDesc I Γ #c
    {γ} : ⟦ Γ ⟧
    {i} : ⟦ I ⟧
    to : A → μ desc γ i
    from : μ desc γ i → A

  quotedDesc : QuotedDesc
  quotedDesc = mk `datatypeName `constructorNames desc
