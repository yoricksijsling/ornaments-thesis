
module Cx.GenericOperations where

open import Common
open import Cx.Named
open import Cx.HasDesc
open HasDesc

gfold : ∀{A}{{R : HasDesc A}} → ∀{X} →
  Alg (desc R) (γ R) X → A → X (i R)
gfold α = fold α ∘ to

gforget : ∀{A}{{AR : HasDesc A}}{B}{{BR : HasDesc B}} →
  ∀ {u c} (o : Orn (I BR) u (Γ BR) c (desc AR)) →
  {{ieq : i AR ≡ u (i BR)}}
  {{γeq : γ AR ≡ c (γ BR)}}
  {{#ceq : #c AR ≡ #c BR}}
  {{deq : transport (DatDesc (I BR) (Γ BR)) #ceq (ornToDesc o) ≡ desc BR}} →
  B → A
gforget {{AR = mk desc Ato Afrom}} {{BR = mk .(ornToDesc o) Bto Bfrom}} o
  {{refl}} {{refl}} {{refl}} {{refl}} = Afrom ∘ forget o ∘ Bto



----------------------------------------
-- Depth

maxNat : Nat → Nat → Nat
maxNat zero n = n
maxNat (suc m) zero = suc m
maxNat (suc m) (suc n) = suc (maxNat m n)

maxNat-id : ∀ n → maxNat n n ≡ n
maxNat-id zero = refl
maxNat-id (suc n) = cong suc (maxNat-id n)

depthAlg : ∀{I Γ dt} → (D : Desc I Γ dt) → ∀{γ} → Alg D γ (λ i → Nat)
depthAlg {dt = isCon} (ι o) v = 0
depthAlg {dt = isCon} (nm / S ⊗ xs) (s , v) = depthAlg xs v
depthAlg {dt = isCon} (nm /rec i ⊗ xs) (sdepth , v) = maxNat (suc sdepth) (depthAlg xs v)
depthAlg {dt = isDat _} D (k , v) = depthAlg (lookupCtor D k) v

gdepth : ∀{A} → {{R : HasDesc A}} → A → Nat
gdepth {{R}} = gfold (depthAlg (desc R))


----------------------------------------
-- Count

-- Count all the nodes, including the leaves

countAlg : ∀{I Γ dt} → (D : Desc I Γ dt) → ∀{γ} → Alg D γ (λ i → Nat)
countAlg {dt = isCon} (ι o) x = 1
countAlg {dt = isCon} (nm / S ⊗ xs) (s , v) = countAlg xs v
countAlg {dt = isCon} (nm /rec i ⊗ xs) (scount , v) = scount + countAlg xs v
countAlg {dt = isDat #c} D (k , v) = countAlg (lookupCtor D k) v

gcount : ∀{A} → {{R : HasDesc A}} → A → Nat
gcount {{R}} = gfold (countAlg (desc R))
