module Stuff where

open import Prelude
open import Container.List

private
  inject₁ : ∀ {m} → Fin m → Fin (suc m)
  inject₁ zero    = zero
  inject₁ (suc i) = suc (inject₁ i)

finReverse : ∀ {n} → Fin n → Fin n
finReverse (zero {zero}) = zero {zero}
finReverse (zero {suc n}) = suc (finReverse zero)
finReverse (suc k) = inject₁ (finReverse k)

private
  test-finReverse07 : finReverse {7} 0 ≡ 6
  test-finReverse07 = refl

  test-finReverse37 : finReverse {7} 3 ≡ 3
  test-finReverse37 = refl

module ZipNats where
  zipNats : ∀{a b}{A : Set a}{B : Set b}
            (f : Nat → A → B) → List A → List B
  zipNats {A = A} {B} f xs = foldr op (const []) xs 0
    where
    op : A → (Nat → List B) → Nat → List B
    op x xs n = (f n x) ∷ (xs (suc n))

  zipNatsDown : ∀{a b}{A : Set a}{B : Set b}
                (offset : Nat) → (f : Nat → A → B) → List A → List B
  zipNatsDown {A = A} {B} offset f xs = fst (foldr op ([] , offset) xs)
    where
    op : A → List B × Nat → List B × Nat
    op x (xs , n) = (f n x ∷ xs) , suc n

  private
    test-zipNats : zipNats (_+_) (10 ∷ 20 ∷ 30 ∷ []) ≡ (10 ∷ 21 ∷ 32 ∷ [])
    test-zipNats = refl

    test-zipNatsDown : zipNatsDown 3 (_+_) (10 ∷ 20 ∷ 30 ∷ []) ≡ (15 ∷ 24 ∷ 33 ∷ [])
    test-zipNatsDown = refl

open ZipNats public
