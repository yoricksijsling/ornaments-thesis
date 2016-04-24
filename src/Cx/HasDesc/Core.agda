
module Cx.HasDesc.Core where

open import Common
open import Reflection

open import Cx.Named
open import Cx.Quoting.QuotedDesc public

record HasDesc (A : Set) : Set₂ where
  constructor mk
  field quotedDesc : QuotedDesc
  open QuotedDesc quotedDesc public
  field
    {γ} : ⟦ Γ ⟧
    {i} : ⟦ I ⟧
    to : A → μ desc γ i
    from : μ desc γ i → A
