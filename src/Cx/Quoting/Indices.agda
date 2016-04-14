
module Cx.Quoting.Indices where

open import Common
open import Reflection
open import Tactic.Reflection

private
  indicesToSigmas : List (Arg Type) → Type
  indicesToSigmas [] = def₀ (quote ⊤)
  indicesToSigmas ((arg _ x) ∷ xs) = def₂ (quote _×_) x (indicesToSigmas xs)

getIndices : Nat → Type → TC Set
getIndices #p = tryUnquoteTC "getIndices" ∘ indicesToSigmas ∘ drop #p ∘ fst ∘ telView
