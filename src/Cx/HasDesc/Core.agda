
module Cx.HasDesc.Core where

open import Common
open import Reflection

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

-- Alternative way of defining |to| and |from|
-- open HasDesc {{...}} renaming (to′ to to; from′ to from) using () public

to : {A : Set} {{r : HasDesc A}} →
  A → μ (HasDesc.desc r) (HasDesc.γ r) (HasDesc.i r)
to {{r}} = HasDesc.to′ r

from : {A : Set} {{r : HasDesc A}} →
  μ (HasDesc.desc r) (HasDesc.γ r) (HasDesc.i r) → A
from {{r}} = HasDesc.from′ r
