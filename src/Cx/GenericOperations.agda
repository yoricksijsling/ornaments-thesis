
module Cx.GenericOperations where

open import Common
open import Cx.Named
open import Cx.HasDesc
open HasDesc

gfold : ∀{A}{{R : HasDesc A}} → ∀{X} → Alg (desc R) (γ R) X → A → X (i R)
gfold α = fold α ∘ to

gforget : ∀{A}{{AR : HasDesc A}}{B}{{BR : HasDesc B}} →
          {u : Cxf (I BR) (I AR)}{c : Cxf (Γ BR) (Γ AR)} →
          (o : Orn u c (desc AR)) →
          {{ieq : i AR ≡ u (i BR)}} {{γeq : γ AR ≡ c (γ BR)}} {{#ceq : #c AR ≡ #c BR}}
          {{deq : transport (DatDesc (I BR) (Γ BR)) #ceq (ornToDesc o) ≡ desc BR}} →
          B → A
gforget {{AR = mk desc Ato Afrom}} {{BR = mk .(ornToDesc o) Bto Bfrom}} o
  {{refl}} {{refl}} {{refl}} {{refl}} = Afrom ∘ forget o ∘ Bto


----------------------------------------
-- Depth

depthAlg : ∀{I Γ dt} → (D : Desc I Γ dt) → ∀{γ} → Alg D γ (λ _ → Nat)
depthAlg {dt = isCon} (ι o) v = 0
depthAlg {dt = isCon} (nm / S ⊗ xs) (s , v) = depthAlg xs v
depthAlg {dt = isCon} (nm /rec i ⊗ xs) (s , v) = max (suc s) (depthAlg xs v)
depthAlg {dt = isDat _} D (k , v) = depthAlg (lookupCtor D k) v

gdepth : ∀{A} → {{R : HasDesc A}} → A → Nat
gdepth {{R}} = gfold (depthAlg (desc R))

-- ----------------------------------------
-- -- Last

-- We can't really see when an element is being used, so stuff like last or sum is not possible. We could solve it by not using functions in ⊗ but some deep embedding which can directly represent parameter references:
--   data ArgFun : Cx → Set where
--     top : ∀{Γ} → ArgFun Γ
--     pop : ∀{S Γ} → ArgFun (S ◁ Γ)
--     fun : (⟦ Γ ⟧ → Set) → ArgFun Γ

-- private
--   lastAlg : ∀{I Γ dt} → (D : Desc I Γ dt) → ∀{γ} → Alg D γ (λ _ → Nat)
--   lastAlg {dt = isCon} (ι o) v = {!!}
--   lastAlg {dt = isCon} (nm / S ⊗ xs) (s , v) = {!!}
--   lastAlg {dt = isCon} (nm /rec i ⊗ xs) (s , v) = {!!}
--   lastAlg {dt = isDat _} D (k , v) = {!!}

-- glast : ∀{A} → {{R : HasDesc A}} → A → Nat
-- glast {{R}} = fold (depthAlg (desc R)) ∘ to R
