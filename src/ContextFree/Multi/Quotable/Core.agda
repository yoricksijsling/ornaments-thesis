module ContextFree.Multi.Quotable.Core where

open import Common
open import ContextFree.Multi.Desc

record RawQuotable (A : Set) : Set₁ where
  constructor mk
  field
    {I} : Set
    {req} : ISet I
    desc : IODesc (Either I ⊤) ⊤
    to : A → ⟦ `fix desc ⟧ req tt
    from : ⟦ `fix desc ⟧ req tt → A

record Quotable (A : Set) : Set₁ where
  constructor mk
  field
    {I} : Set
    {req} : ISet I
    desc : IODesc (Either I ⊤) ⊤
    to : A → ⟦ `fix desc ⟧ req tt
    from : ⟦ `fix desc ⟧ req tt → A
    to-from : ∀ x → from (to x) ≡ x
    from-to : ∀ x → to (from x) ≡ x
