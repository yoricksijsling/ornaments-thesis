module Reflection where

open import Common
open import Builtin.Reflection public
open import Tactic.Reflection public

{-# DISPLAY arg (arg-info visible relevant) x = vArg x #-}
{-# DISPLAY arg (arg-info hidden relevant) x = hArg x #-}
{-# DISPLAY arg (arg-info instance′ relevant) x = iArg x #-}

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

forceType : ∀{a} (A : Set a) → A → A
forceType A x = x

`forceType : Type → Term → Term
`forceType `A `x = def₂ (quote forceType) `A `x

forceTypeTC : ∀{a}{A : Set a} → A → Term → TC Term
forceTypeTC A tm = flip `forceType tm <$> quoteTC A

private
  beforeDot : List Char → List Char
  beforeDot [] = []
  beforeDot (c ∷ cs) = if eqChar c '.'
                       then []
                       else c ∷ beforeDot cs
showNameInModule : Name → String
showNameInModule = packString ∘ reverse ∘ beforeDot ∘ reverse ∘ unpackString ∘ show


----------------------------------------
-- TC convenience functions

fromMaybe′ : ∀{a}{A : Set a} → List ErrorPart → Maybe A → TC A
fromMaybe′ e (just x) = return x
fromMaybe′ e nothing = typeError e

fromMaybe : ∀{a}{A : Set a} → String → Maybe A → TC A
fromMaybe s = fromMaybe′ [ strErr s ]

tryUnquoteTC : ∀{a}{A : Set a} → String → Term → TC A
tryUnquoteTC {A = A} s tm = catchTC (unquoteTC tm) (quoteTC A >>=′ λ `A →
  typeError (strErr s ∷ strErr "failed to unquote" ∷ termErr tm ∷ strErr "to type" ∷ termErr `A ∷ []))

ShouldFail : ∀{a}{A : Set a} → TC A → TC Set
ShouldFail tc = catchTC (tc >>=′ λ _ → return ⊥) (return ⊤)

macro
  ShouldFailᵐ : ∀{a}{A : Set a} → TC A → Tactic
  ShouldFailᵐ tc = evalTC (ShouldFail tc)

giveTC : TC Term → Tactic
giveTC tm hole = tm >>= give hole

macro
  giveT : TC Term → Tactic
  giveT = giveTC


----------------------------------------
-- Telescopes which remember names

AbsTelescope = List (Abs (Arg Type))

absTelescope : Type → AbsTelescope × Type
absTelescope (pi (arg i x) (abs s xs)) = first (_∷_ (abs s (arg i x))) (absTelescope xs)
absTelescope xs = [] , xs

absTelPi : AbsTelescope → Type → Type
absTelPi tel xs = foldr (λ { (abs s (arg i x)) xs → pi (arg i x) (abs s xs)}) xs tel

absTelView : (t : Type) → Σ AbsTelescope λ tel → Σ Type λ xs → absTelPi tel xs ≡ t
absTelView (pi (arg i x) (abs s xs)) with absTelView xs
absTelView (pi (arg i x) (abs s _)) | rtel , rxs , refl = (abs s (arg i x)) ∷ rtel , rxs , refl
absTelView xs = [] , xs , refl
