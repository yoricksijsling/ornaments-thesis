
module Cx.HasDesc.Core where

open import Common
open import Reflection

open import Cx.Quoting.QuotedDesc public
open import Cx.Named

record HasDesc (A : Set) : Set₂ where
  constructor mk
  field
    {I Γ} : Cx
    {#c} : Nat
    desc : DatDesc I Γ #c
    {γ} : ⟦ Γ ⟧
    {i} : ⟦ I ⟧
    to′ : A → μ desc γ i
    from′ : μ desc γ i → A

open HasDesc

to : {A : Set} {{r : HasDesc A}} → A → μ (desc r) (γ r) (i r)
to {{r}} = to′ r
from : {A : Set} {{r : HasDesc A}} → μ (desc r) (γ r) (i r) → A
from {{r}} = from′ r