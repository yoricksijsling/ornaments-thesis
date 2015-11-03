module Stuff where

open import Data.List using (List; []; _∷_)
open import Data.List.All using (All; []; _∷_)

foldrWithDefault : ∀ {a} {A : Set a} → A → (A → A → A) → List A → A
foldrWithDefault d f [] = d
foldrWithDefault d f (x ∷ []) = x
foldrWithDefault d f (x ∷ y ∷ ys) = f x (foldrWithDefault d f (y ∷ ys))


mapAllToList : ∀{a p b}{A : Set a}{P : A → Set p}{B : Set b} →
               (f : ∀{x} → P x → B) → {xs : List A} → All P xs → List B
mapAllToList f [] = []
mapAllToList f (x ∷ xs) = (f x) ∷ (mapAllToList f xs)

-- module ListMin where
--   open import Data.Nat
--   import Data.Nat.Properties as NP
--   import Relation.Binary as RB
--   open module dto = RB.DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)

--   listMin : (xs : List ℕ) → ∃ λ min → All (_≤_ min) xs
--   listMin [] = zero , []
--   listMin (x ∷ xs) with listMin xs
--   listMin (x ∷ xs) | rmin , rp with compare rmin x
--   listMin (.(suc (rmin + k)) ∷ xs) | rmin , rp | less .rmin k = rmin , NP.≤-step (NP.m≤m+n rmin k) ∷ rp
--   listMin (rmin ∷ xs)              | .rmin , rp | equal .rmin = rmin , ≤-refl ∷ rp
--   listMin (x ∷ xs)                 | .(suc (x + k)) , rp | greater .x k = x , ≤-refl ∷ (Data.List.All.map l rp)
--     where l : {y : ℕ} → suc (x + k) ≤ y → x ≤ y
--           l = ≤-trans (NP.≤-step (NP.m≤m+n x k))
-- open ListMin
