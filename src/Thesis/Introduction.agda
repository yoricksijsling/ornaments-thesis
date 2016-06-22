
module Thesis.Introduction where

open import Common hiding (List; sum; Vec; min; take)

infixr 5 _∷_
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

take : ∀{A} → Nat → List A → List A
take zero    _        = []
take (suc n) []       = {!!}
take (suc n) (x ∷ xs) = x ∷ take n xs

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

takeᵥ : ∀{A m} → (n : Nat) → Vec A (n + m) → Vec A n
takeᵥ zero _ = []
takeᵥ (suc n) (x ∷ xs) = x ∷ takeᵥ n xs

--------------------

find : List Nat → (P : Nat → Bool) → Maybe Nat
find [] P = nothing
find (x ∷ xs) P = if (P x) then (just x) else (find xs P)

findᵥ : ∀{n} → Vec Nat n → (P : Nat → Bool) → Maybe Nat
findᵥ [] P = nothing
findᵥ (x ∷ xs) P = if (P x) then (just x) else (findᵥ xs P)

--

data BoundedNatList (mx : Nat) : Set where
  [] : BoundedNatList mx
  _∷_ : (x : Nat) {{p : IsTrue (x ≤? mx)}} →
    (xs : BoundedNatList mx) → BoundedNatList mx

data SortedNatList : (l : Nat) → Set where
  [] : ∀{l} → SortedNatList l
  _∷_ : ∀{l} → (x : Nat) {{p : IsTrue (x ≤? l)}} →
    (xs : SortedNatList l) → SortedNatList x

find_b : ∀{mx} → BoundedNatList mx → (P : Nat → Bool) → Maybe Nat
find_b [] P = nothing
find_b (x ∷ xs) P = if (P x) then (just x) else (find_b xs P)

find_s : ∀{l} → SortedNatList l → (P : Nat → Bool) → Maybe Nat
find_s [] P = nothing
find_s (x ∷ xs) P = if (P x) then (just x) else (find_s xs P)

--------------------

-- _++_ : ∀{A} → List A → List A → List A
-- []       ++ ys = ys
-- (x ∷ xs) ++ ys = x ∷ xs ++ ys

-- _++ᵥ_ : ∀{A m n} → Vec A m → Vec A n → Vec A (m + n)
-- []       ++ᵥ ys = ys
-- (x ∷ xs) ++ᵥ ys = x ∷ (xs ++ᵥ ys)

data Desc : Set where
  `1 : Desc
  _⊕_ : Desc → Desc → Desc
  _⊗_ : Desc → Desc → Desc

⟦_⟧desc : Desc → Set
⟦ `1 ⟧desc = ⊤
⟦ A ⊕ B ⟧desc = Either ⟦ A ⟧desc ⟦ B ⟧desc
⟦ A ⊗ B ⟧desc = ⟦ A ⟧desc × ⟦ B ⟧desc

bool-to : Bool → ⟦ `1 ⊕ `1 ⟧desc
bool-to false = left tt
bool-to true = right tt

bool-from : ⟦ `1 ⊕ `1 ⟧desc → Bool
bool-from (left tt) = false
bool-from (right tt) = true
