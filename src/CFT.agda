module CFT where

-- 1) type def voor CFT
-- 2) semantiek ⟦_⟧ : CFT → Set
-- 3) generieke fns decEq, gmap, ...
-- 4) record IsCFT (a : Set)
--      code : CFT
--      to : a → ⟦ CFT ⟧
--      from : ⟦ CFT ⟧ → a
-- 5) gmap : {a : Set} → ⦃ IsCFT a ⦄ → ...
-- 6) quotation
--    isCFT-YT : IsCFT YT
--    isCFT-YT = unquoteDecl ... quote YT ...

-- CFT : 0, 1, x, +, μ, def, wk, vl, →, fun

open import Data.Bool
open import Data.Empty
open import Data.Fin
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality

data RIDesc (I : Set) : Set₁ where
  `var : (i : I) → RIDesc I -- wk and vl
  `1 : RIDesc I
  `Σ : (S : Set)(T : S → RIDesc I) → RIDesc I -- k, 0, × and +
  _`→_ : (S : Set)(T : S → RIDesc I) → RIDesc I

  -- Σ makes these redundant:
  `0 : RIDesc I
  `k : (A : Set) → RIDesc I
  _`×_ : (A B : RIDesc I) → RIDesc I
  _`+_ : (A B : RIDesc I) → RIDesc I
  `σ : (n : ℕ)(T : Fin n → RIDesc I) → RIDesc I

  -- `μ : (f : CFT (suc n)) → RIDesc I
  -- Internal fixpoints are not supported (See Gentle Art of Levitation §6.4)


⟦_⟧r : {I : Set} → RIDesc I → (I → Set) → Set
⟦ `var i ⟧r X = X i
⟦ `1 ⟧r X = ⊤
⟦ `Σ S T ⟧r X = Σ S λ s → ⟦ T s ⟧r X
⟦ S `→ T ⟧r X = (s : S) → ⟦ T s ⟧r X
⟦ `0 ⟧r X = ⊥
⟦ `k A ⟧r X = A
⟦ A `× B ⟧r X = ⟦ A ⟧r X × ⟦ B ⟧r X
⟦ A `+ B ⟧r X = Σ Bool λ { true → ⟦ A ⟧r X ; false → ⟦ B ⟧r X }
⟦ `σ n T ⟧r X = Σ (Fin n) λ k → ⟦ T k ⟧r X

⟦_⟧rmap : {I : Set} {X Y : I → Set} (D : RIDesc I) → (f : ∀ {i} → X i → Y i) → ⟦ D ⟧r X → ⟦ D ⟧r Y
⟦_⟧rmap (`var i) f xs = f xs
⟦_⟧rmap `1 f tt = tt
⟦_⟧rmap (`Σ S T) f (s , xs) = s , ⟦ T s ⟧rmap f xs
⟦_⟧rmap (S `→ T) f xs s = ⟦ T s ⟧rmap f (xs s)
⟦_⟧rmap `0 f ()
⟦_⟧rmap (`k A) f xs = xs
⟦_⟧rmap (A `× B) f (a , b) = ⟦ A ⟧rmap f a , ⟦ B ⟧rmap f b
⟦_⟧rmap (A `+ B) f (true , xs) = true , ⟦ A ⟧rmap f xs
⟦_⟧rmap (A `+ B) f (false , xs) = false , ⟦ B ⟧rmap f xs
⟦_⟧rmap (`σ n T) f (k , xs) = k , ⟦ T k ⟧rmap f xs


-- RIDesc is only one description, but the required description can be dependent
-- on the given index. (e.g. Vec A 2 has an other description than Vec A 0).

record IDesc (I : Set) : Set₁ where
  constructor mk
  field
    _at_ : I → RIDesc I

open IDesc

-- Note how this interpretation gives us an endofunctor on Setⁱ.
⟦_⟧ : {I : Set} → IDesc I → (I → Set) → (I → Set)
⟦ D ⟧ X i = ⟦ D at i ⟧r X

⟦_⟧map : {I : Set}{X Y : I → Set} (D : IDesc I) → (f : ∀{i} → X i → Y i) →
  ∀{i} → ⟦ D ⟧ X i → ⟦ D ⟧ Y i
⟦_⟧map D f x = ⟦ D at _ ⟧rmap f x

module Redundancies where
  open import Function.Inverse as FI using (_↔_)

  ⟦⟧-eq : {I : Set}(X : I → Set)(A B : RIDesc I) → Set
  ⟦⟧-eq {I} X A B = ⟦ A ⟧r X ↔ ⟦ B ⟧r X

  `0-redundant : ∀{I}(X : I → Set) → ⟦⟧-eq X `0 (`Σ ⊥ ⊥-elim)
  `0-redundant X = record
    { to = →-to-⟶ ⊥-elim
    ; from = →-to-⟶ λ { (() , _) }
    ; inverse-of = record { left-inverse-of = λ { () }
                          ; right-inverse-of = λ { (() , _) }
                          }
    }

  `k-redundant : ∀{I K}(X : I → Set) → ⟦⟧-eq X (`k K) (`Σ K (const `1))
  `k-redundant X = record
    { to = →-to-⟶ (λ k → k , tt)
    ; from = →-to-⟶ λ { (k , tt) → k }
    ; inverse-of = record { left-inverse-of = λ _ → refl
                          ; right-inverse-of = λ _ → refl
                          }
    }

  `×-redundant : ∀{I A B} (X : I → Set) → ⟦⟧-eq X (A `× B) (`Σ (⟦ A ⟧r X) (const B))
  `×-redundant X = FI.id

  `+-redundant : ∀{I A B} (X : I → Set) →
    ⟦⟧-eq X (A `+ B) (`Σ Bool λ { true → A ; false → B })
  `+-redundant X = record
    { to = →-to-⟶ λ { (true , a) → true , a ; (false , b) → false , b }
    ; from = →-to-⟶ λ { (true , a) → true , a ; (false , b) → false , b }
    ; inverse-of = record
      { left-inverse-of = λ { (true , _) → refl ; (false , _) → refl }
      ; right-inverse-of = λ { (true , _) → refl ; (false , _) → refl }
      }
    }

  `σ-redundant : ∀{I n}{T : Fin n → RIDesc I} (X : I → Set) →
    ⟦⟧-eq X (`σ n T) (`Σ (Fin n) T)
  `σ-redundant X = FI.id

data μ {I} (D : IDesc I)(i : I) : Set where
  ⟨_⟩ : ⟦ D ⟧ (μ D) i → μ D i
