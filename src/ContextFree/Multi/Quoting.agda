module ContextFree.Multi.Quoting where

open import Builtin.Reflection
open import Common
open import Container.Traversable
open import TC

open import ContextFree.Multi.Desc
open import ContextFree.Multi.Params
open import ContextFree.Multi.Quoted
open import ContextFree.Multi.Quoting.Constructor

quoteDatatype : (`dt : Name) → TC NamedSafeDatatype
quoteDatatype `dt =
  do dtty ← getType `dt
  -| pc ← getParameters `dt
  -| params ← iguard (fst $ takeParams dtty pc) "Too many parameters for datatype"
  -| cnames ← getConstructors `dt
  -| (mk `dt params []) <$> mapM (quoteConstructor `dt pc) cnames

macro
  quoteDatatypeᵐ : (`dt : Name) → Tactic
  quoteDatatypeᵐ `dt = runTC (quoteDatatype `dt)



-- PARAMETERS / INDICES

-- data ListP (A : Set) : Set where
--   nilP : ListP A
--   consP : A → ListP A → ListP A

-- data ListI : (A : Set) → Set₁ where
--   nilI : ∀{A} → ListI A
--   consI : ∀{A} → A → ListI A → ListI A

-- type (quote Dummy)  ≡ el₁ (sort (lit 0))
-- type (quote ListP)  ≡ el₁ (pi (argvr (el₁ (sort (lit 0))))
--                               (el₁ (sort (lit 0))))
-- type (quote ListI)  ≡ el₂ (pi (argvr (el₁ (sort (lit 0))))
--                               (el₂ (sort (lit 1))))
-- type (quote nilP)   ≡ el₁ (pi (arghr (el₁ (sort (lit 0))))
--                               (el₀ (def (quote ListP) (argvr (var 0 []) ∷ []))))
-- type (quote nilI)   ≡ el₁ (pi (arghr (el₁ (sort (lit 0))))
--                               (el₁ (def (quote ListI) (argvr (var 0 []) ∷ []))))
