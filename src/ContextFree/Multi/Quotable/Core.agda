module ContextFree.Multi.Quotable.Core where

open import Common
open import ContextFree.Multi.Desc

record RawQuotable (A : Set) : Set₁ where
  constructor mk
  field
    {I O} : Set
    {req} : ISet I
    {o} : O
    desc : IODesc I O
    to : A → ⟦ desc ⟧ req o
    from : ⟦ desc ⟧ req o → A

record Quotable (A : Set) : Set₁ where
  constructor mk
  field
    {I O} : Set
    {req} : ISet I
    {o} : O
    desc : IODesc I O
    to : A → ⟦ desc ⟧ req o
    from : ⟦ desc ⟧ req o → A
    to-from : ∀ x → from (to x) ≡ x
    from-to : ∀ x → to (from x) ≡ x
