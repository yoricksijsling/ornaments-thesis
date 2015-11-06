module Stuff where

open import Data.List using (List; []; _∷_)
open import Data.List.All using (All; []; _∷_)

mapAllToList : ∀{a p b}{A : Set a}{P : A → Set p}{B : Set b} →
               (f : ∀{x} → P x → B) → {xs : List A} → All P xs → List B
mapAllToList f [] = []
mapAllToList f (x ∷ xs) = (f x) ∷ (mapAllToList f xs)

module ZipStream where
  open import Coinduction using (♭)
  open import Data.Stream using (Stream; _∷_)
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open import Data.List using (foldl; foldr)

  zipStream : ∀{a c}{A : Set a}{B : Set}{C : Set c}(f : A → B → C) →
              List A → Stream B → List C
  zipStream {A = A} {B} {C} f xs ys = foldr op (λ _ → []) xs ys
    where
    op : A → (Stream B → List C) → Stream B → List C
    op x xs (y ∷ ys) = (f x y) ∷ xs (♭ ys)

  zipStreamBackwards : ∀{a c}{A : Set a}{B : Set}{C : Set c}(f : A → B → C) →
              List A → Stream B → List C
  zipStreamBackwards {A = A} {B} {C} f xs ys = proj₁ (foldr op ([] , ys) xs)
    where
    op : A → List C × Stream B → List C × Stream B
    op x (xs , y ∷ ys) = (f x y) ∷ xs , ♭ ys

open ZipStream public

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
