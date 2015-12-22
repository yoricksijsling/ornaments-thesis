module IODesc where

open import Data.Empty
open import Data.Unit.Base
open import Data.Sum
open import Data.Product
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality

infixr 3 _`+_
infixr 4 _`*_

IOFunc : Set → Set → Set₁
IOFunc I O = (I → Set) → (O → Set)

_or_ : {I J : Set} → (I → Set) → (J → Set) → (I ⊎ J) → Set
(r or s) (inj₁ i) = r i
(r or s) (inj₂ j) = s j

mutual
  data IODesc : Set → Set → Set₁ where
    `0 : ∀{I O} → IODesc I O
    `1 : ∀{I O} → IODesc I O
    _`+_ : ∀{I O} → (A B : IODesc I O) → IODesc I O
    _`*_ : ∀{I O} → (A B : IODesc I O) → IODesc I O
    `var : ∀{I O} → I → IODesc I O
    `! : ∀{I O} → O → IODesc I O
    `Fix : ∀{I O} → IODesc (I ⊎ O) O → IODesc I O
    `Σ : ∀{I O} → {C : IODesc ⊥ ⊤} →
         (f : ⟦ C ⟧ (λ ()) tt → IODesc I O) → IODesc I O
    -- `Iso : ∀{I O} → (C : IODesc I O) → (D : IOFunc I O) → IODesc I O
    `Iso : ∀{O} → (C : IODesc ⊥ O) → (D : IOFunc ⊥ O) → IODesc ⊥ O
           -- ((r : I → Set) → (o : O) → D r o ≡ ⟦ C ⟧ r o) → IODesc I O

  data μ {I O : Set} (F : IODesc (I ⊎ O) O)
         (r : I → Set) (o : O) : Set where
    ⟨_⟩ : ⟦ F ⟧ (r or μ F r) o → μ F r o

  ⟦_⟧ : ∀{I O} → IODesc I O → IOFunc I O
  ⟦_⟧ `0 r o = ⊥
  ⟦_⟧ `1 r o = ⊤
  ⟦_⟧ (A `+ B) r o = ⟦ A ⟧ r o ⊎ ⟦ B ⟧ r o
  ⟦_⟧ (A `* B) r o = ⟦ A ⟧ r o × ⟦ B ⟧ r o
  ⟦_⟧ (`var I) r o = r I
  ⟦_⟧ (`! o′) r o = o ≡ o′
  ⟦_⟧ (`Fix F) r o = μ F r o
  ⟦_⟧ (`Σ f) r o = ∃ (λ i → ⟦ f i ⟧ r o)
  -- ⟦_⟧ (`Iso C D) r o = D r o
  ⟦_⟧ (`Iso C D) r o = D (λ ()) o

-- r kan μ bevatten, en door D toe te passen komt die op een negatieve positie.
-- ⟦_⟧ mag geen dingen opleveren met 

data Orn : (I O : Set) → IODesc I O → Set₁ where
  `0 : ∀{I O} → Orn I O `0
  `1 : ∀{I O} → Orn I O `1
  _`+_ : ∀{I O}{A B : IODesc I O} → Orn I O A → Orn I O B → Orn I O (A `+ B)
  _`*_ : ∀{I O}{A B : IODesc I O} → Orn I O A → Orn I O B → Orn I O (A `* B)
  insert : ∀{I O}(A : IODesc I O){B : IODesc I O} → Orn I O B → Orn I O (A `* B)



-- Parameters

PairDesc : IODesc (⊤ ⊎ ⊤) ⊤
PairDesc = `var (inj₁ tt) `* `var (inj₂ tt)

select : (A B : Set) → ⊤ ⊎ ⊤ → Set
select A B (inj₁ tt) = A
select A B (inj₂ tt) = B

pairOk : (A B : Set) → ⟦ PairDesc ⟧ (select A B) tt ≡ (A × B)
pairOk A B = refl

-- Recursive types
ℕDesc : ∀{I} → IODesc I ⊤
ℕDesc = `Fix (`1 `+ `var (inj₂ tt))

ListFDesc : IODesc (⊤ ⊎ ⊤) ⊤
ListFDesc = `1 `+ (`var (inj₁ tt) `* `var (inj₂ tt))

ListDesc : IODesc ⊤ ⊤
ListDesc = `Fix ListFDesc

fromList : ∀{A} → List A → ⟦ ListDesc ⟧ (λ _ → A) tt
fromList [] = ⟨ inj₁ tt ⟩
fromList (x ∷ xs) = ⟨ inj₂ (x , fromList xs) ⟩

-- Simple indexing
open import Data.Nat
-- data Fin : ℕ → Set where
--   Fin (suc n) ∋ zero
--               | suc : (i : Fin n)
data Fin : ℕ → Set where
  zero : ∀{n} → Fin (suc n)
  suc : ∀{n} (i : Fin n) → Fin (suc n)

FinFDesc : ℕ → IODesc (⊥ ⊎ ℕ) ℕ
FinFDesc zero = `! zero `* `0
FinFDesc (suc n) = `! (suc n) `* (`1 `+ `var (inj₂ n))

FinFDesc′ : IODesc (⊥ ⊎ ℕ) ℕ
FinFDesc′ = `Σ {C = `Iso ℕDesc (λ _ _ → ℕ)} FinFDesc

FinDesc : IODesc ⊥ ℕ
FinDesc = `Fix FinFDesc′

-- fromFin : ∀{n} → Fin n → ⟦ FinDesc ⟧ (λ ()) n
-- -- fromFin {suc n} (suc k) = ⟨ n , refl , inj₂ (fromFin {n} k) ⟩
-- fromFin {suc n} zero = ⟨ suc n , refl , inj₁ tt ⟩
-- fromFin {suc n} (suc k) = ⟨ suc n , refl , inj₂ (fromFin k) ⟩

-- toFin : ∀{n} → ⟦ FinDesc ⟧ (λ ()) n → Fin n
-- toFin ⟨ zero , refl , () ⟩
-- toFin ⟨ suc n , refl , inj₁ tt ⟩ = zero
-- toFin ⟨ suc n , refl , inj₂ y ⟩ = suc (toFin {!y!})

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

VecFDesc : ℕ → IODesc (⊤ ⊎ ℕ) ℕ
VecFDesc zero = `! zero
VecFDesc (suc n) = `! (suc n) `* `var (inj₁ tt) `* `var (inj₂ n)

VecDesc : IODesc ⊤ ℕ
VecDesc = `Fix (`Σ {C = `Iso ℕDesc (λ _ _ → ℕ)} VecFDesc)

fromVec : ∀{A n} → Vec A n → ⟦ VecDesc ⟧ (λ _ → A) n
fromVec [] = ⟨ 0 , refl ⟩
fromVec {n = suc n} (x ∷ xs) = ⟨ suc n , refl , x , fromVec xs ⟩

-- Mutually recursive types
mutual
  data Tree (A : Set) : Set where
    empty : Tree A
    node : A → Forest A → Tree A
  data Forest (A : Set) : Set where
    nil : Forest A
    cons : Tree A → Forest A → Forest A

data WoodTag : Set where
  tree forest : WoodTag

data Wood (A : Set) : WoodTag → Set where
  empty : Wood A tree
  node  : A → Wood A forest → Wood A tree
  nil   : Wood A forest
  cons  : Wood A tree → Wood A forest → Wood A forest

-- indexfirst data Wood (A : Set) : WoodTag → Set where
--   Wood A tree   ∋ empty
--                 | node   (x : A) (f : Wood A forest)
--   Wood A forest ∋ nil
--                 | cons   (t : Wood A tree) (f : Wood A forest)



TreeDescF : IODesc (⊤ ⊎ WoodTag) WoodTag
TreeDescF = `1
         `+ `var (inj₁ tt) `* `var (inj₂ forest)

ForestDescF : IODesc (⊤ ⊎ WoodTag) WoodTag
ForestDescF = `1
           `+ `var (inj₂ tree) `* `var (inj₂ forest)

WoodDescF : IODesc (⊤ ⊎ WoodTag) WoodTag
WoodDescF = `! tree `* TreeDescF
         `+ `! forest `* ForestDescF

WoodDesc : IODesc ⊤ WoodTag
WoodDesc = `Fix WoodDescF

mutual
  Wood→Tree : ∀{A} → Wood A tree → Tree A
  Wood→Tree empty = empty
  Wood→Tree (node x f) = node x (Wood→Forest f)
  Wood→Forest : ∀{A} → Wood A forest → Forest A
  Wood→Forest nil = nil
  Wood→Forest (cons t f) = cons (Wood→Tree t) (Wood→Forest f)

mutual
  fromTree : ∀{A} → Tree A → ⟦ WoodDesc ⟧ (λ _ → A) tree
  fromTree empty = ⟨ inj₁ (refl , inj₁ tt) ⟩
  fromTree (node x f) = ⟨ inj₁ (refl , inj₂ (x , fromForest f)) ⟩
  fromForest : ∀{A} → Forest A → ⟦ WoodDesc ⟧ (λ _ → A) forest
  fromForest nil = ⟨ inj₂ (refl , inj₁ tt) ⟩
  fromForest (cons t f) = ⟨ inj₂ (refl , inj₂ (fromTree t , fromForest f)) ⟩

  toTree : ∀{A} → ⟦ WoodDesc ⟧ (λ _ → A) tree → Tree A
  toTree ⟨ inj₁ (refl , inj₁ tt) ⟩ = empty
  toTree ⟨ inj₁ (refl , inj₂ (x , f)) ⟩ = node x (toForest f)
  toTree ⟨ inj₂ (() , _) ⟩
  toForest : ∀{A} → ⟦ WoodDesc ⟧ (λ _ → A) forest → Forest A
  toForest ⟨ inj₁ (() , _) ⟩
  toForest ⟨ inj₂ (refl , inj₁ tt) ⟩ = nil
  toForest ⟨ inj₂ (refl , inj₂ (t , f)) ⟩ = cons (toTree t) (toForest f)
