
module Thesis.Introduction where

open import Common hiding (List; sum; Vec; min)

infixr 5 _∷_
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

lowest : List Nat → Maybe Nat
lowest [] = nothing
lowest (x ∷ xs) with lowest xs
lowest (x ∷ _) | nothing = just x
lowest (x ∷ _) | just m = just (if (lessNat x m) then x else m)

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

lowestᵥ : ∀{n} → Vec Nat n → Maybe Nat
lowestᵥ [] = nothing
lowestᵥ (x ∷ xs) with lowestᵥ xs
lowestᵥ (x ∷ _) | nothing = just x
lowestᵥ (x ∷ _) | just m = just (if (lessNat x m) then x else m)


-- _++_ : ∀{A} → List A → List A → List A
-- []       ++ ys = ys
-- (x ∷ xs) ++ ys = x ∷ xs ++ ys

-- _++ᵥ_ : ∀{A m n} → Vec A m → Vec A n → Vec A (m + n)
-- []       ++ᵥ ys = ys
-- (x ∷ xs) ++ᵥ ys = x ∷ (xs ++ᵥ ys)

-- take : ∀{A} → Nat → List A → List A
-- take zero    _        = []
-- take (suc n) []       = {!!}
-- take (suc n) (x ∷ xs) = x ∷ take n xs

-- takeᵥ : ∀{A m} → (n : Nat) → Vec A (n + m) → Vec A n
-- takeᵥ zero _ = []
-- takeᵥ (suc n) (x ∷ xs) = x ∷ takeᵥ n xs
