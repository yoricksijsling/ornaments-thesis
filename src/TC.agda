module TC where

open import Prelude
open import Reflection

evalTC : ∀ {a} {A : Set a} → TC A → Tactic
evalTC {A = A} c hole =
  do v ← c
  =| `v ← quoteTC v
  -| `A ← quoteTC A
  -| checkedHole ← checkType hole `A
  -| unify checkedHole `v

-- Use as follows:
-- macro
--   countConstructors′ : Name → Tactic
--   countConstructors′ dt = runTC (length <$> getConstructors dt)

fail : ∀{a}{A : Set a} → String → TC A
fail s = typeErrorS s

fromMaybe : ∀{a}{A : Set a} → String → Maybe A → TC A
fromMaybe s (just x) = return x
fromMaybe s nothing = fail s

iguard : ∀{a}{A : Set a}{p : Bool} → ({{_ : IsTrue p}} → A) → String → TC A
iguard {p = false} f s = fail s
iguard {p = true} f s = return f
