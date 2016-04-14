
module Cx.Quotable.Core where

open import Common
open import Cx.Named

record Quotable (A : Set) : Set₂ where
  constructor mk
  field
    {I} : Set
    {Γ} : Cx
    {#c} : Nat
    {γ} : ⟦ Γ ⟧
    {i} : I
    desc : DatDesc I Γ #c
    to : A → μ desc γ i
    from : μ desc γ i → A
