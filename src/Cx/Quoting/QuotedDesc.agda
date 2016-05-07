
module Cx.Quoting.QuotedDesc where

open import Common
open import Reflection

open import Cx.Named

-- Represents a datatype declaration including names
record QuotedDesc (Nm : Set) : Set₂ where
  constructor mk
  field
    {I} : Cx
    {Γ} : Cx
    {#c} : Nat
    `datatypeName : Nm
    `constructorNames : Vec Nm #c
    desc : DatDesc I Γ #c

instance
  QuotedDesc-functor : Functor QuotedDesc
  QuotedDesc-functor =
    record { fmap = λ { f (mk `dt `cs desc) → mk (f `dt) (fmap f `cs) desc } }
