module Reflection where

open import Common
open import Builtin.Reflection public

pattern set₀ = agda-sort (lit 0)

infixr 4 _`→_
_`→_ : Type → Type → Type
_`→_  a b = pi (vArg a) (abs "_" b)

-- Some things can be used as both a term or a pattern, the TP universe is used
-- to encode this fact.

data TP : Set where
  tp-term : TP
  tp-patt : TP

⟦_⟧tp : TP → Set
⟦_⟧tp tp-term = Term
⟦_⟧tp tp-patt = Pattern

private
  tpf : ∀{tp} → (List (Arg Term) → Term) →
               (List (Arg Pattern) → Pattern) →
               List ⟦ tp ⟧tp → ⟦ tp ⟧tp
  tpf {tp-term} ft fp = ft ∘ map vArg
  tpf {tp-patt} ft fp = fp ∘ map vArg

`conₓ : ∀{tp} → Name → List ⟦ tp ⟧tp → ⟦ tp ⟧tp
`conₓ n = tpf (con n) (con n)
`con₀ : ∀{tp} → Name → ⟦ tp ⟧tp
`con₀ n = `conₓ n []
`con₁ : ∀{tp} → Name → ⟦ tp ⟧tp → ⟦ tp ⟧tp
`con₁ n t₁ = `conₓ n (t₁ ∷ [])
`con₂ : ∀{tp} → Name → ⟦ tp ⟧tp → ⟦ tp ⟧tp → ⟦ tp ⟧tp
`con₂ n t₁ t₂ = `conₓ n (t₁ ∷ t₂ ∷ [])
`con₃ : ∀{tp} → Name → ⟦ tp ⟧tp → ⟦ tp ⟧tp → ⟦ tp ⟧tp → ⟦ tp ⟧tp
`con₃ n t₁ t₂ t₃ = `conₓ n (t₁ ∷ t₂ ∷ t₃ ∷ [])

`varₓ : ∀{tp} → Nat → String → List ⟦ tp ⟧tp → ⟦ tp ⟧tp
`varₓ n s = tpf (var n) (const (var s))
`var₀ : ∀{tp} → Nat → String → ⟦ tp ⟧tp
`var₀ n s = `varₓ n s []

`defₓ : Name → List Term → Term
`defₓ n = def n ∘ map vArg
`def₀ : Name → Term
`def₀ n = `defₓ n []
`def₁ : Name → Term → Term
`def₁ n t₁ = `defₓ n (t₁ ∷ [])
`def₂ : Name → Term → Term → Term
`def₂ n t₁ t₂ = `defₓ n (t₁ ∷ t₂ ∷ [])
`def₃ : Name → Term → Term → Term → Term
`def₃ n t₁ t₂ t₃ = `defₓ n (t₁ ∷ t₂ ∷ t₃ ∷ [])
