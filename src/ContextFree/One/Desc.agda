module ContextFree.One.Desc where

open import Data.Empty
open import Data.Unit.Base
open import Data.Sum
open import Data.Product
open import Data.Nat

-- Internal fixpoints in context free types can be extracted to create a separate
-- description. Given for example:

--   List Nat ≡ μX. 1 + (μY. 1 + Y) * X

-- We can extract the fixpoint, giving us two types (separated by a ,).

--   μX. 1 + Y * X , μY. 1 + Y

-- A bunch of types which may be mutually recursive can be encoded using an
-- indexed fixpoint, a slight generalization of MultiRec.

-- One variable, not dependently typed
data Desc : Set₁ where
  `K : (S : Set) → Desc
  _`+_ : (A B : Desc) → Desc
  _`*_ : (A B : Desc) → Desc
  `var : Desc

`0 : Desc
`0 = `K ⊥

`1 : Desc
`1 = `K ⊤

⟦_⟧ : Desc → Set → Set
⟦_⟧ (`K S) X = S
⟦_⟧ (A `+ B) X = ⟦ A ⟧ X ⊎ ⟦ B ⟧ X
⟦_⟧ (A `* B) X = ⟦ A ⟧ X × ⟦ B ⟧ X
⟦_⟧ `var X = X

data μ (D : Desc) : Set where
  ⟨_⟩ : ⟦ D ⟧ (μ D) → μ D

open import Category.Functor
open RawFunctor
⟦⟧-functor : ∀ D → RawFunctor ⟦ D ⟧
⟦⟧-functor (`K S) = record { _<$>_ = λ f x → x }
⟦⟧-functor (A `+ B) = record { _<$>_ = λ f → Data.Sum.map (_<$>_ (⟦⟧-functor A) f)
                                                          (_<$>_ (⟦⟧-functor B) f) }
⟦⟧-functor (A `* B) = record { _<$>_ = λ f → Data.Product.map (_<$>_ (⟦⟧-functor A) f)
                                                              (_<$>_ (⟦⟧-functor B) f) }
⟦⟧-functor `var = record { _<$>_ = λ f → f }

module Test where
  `nat : Desc
  `nat = `1 `+ `var
  `list : Set → Desc
  `list A = `1 `+ (`K A `* `var)

  natval : μ `nat
  natval = ⟨ inj₂ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ ⟩


open import Relation.Binary.PropositionalEquality using (_≡_)

record IsContextFree (A : Set) : Set₁ where
  field
    desc : Desc
    to : A → μ desc
    from : μ desc → A
    to-from : ∀ x → from (to x) ≡ x
    from-to : ∀ x → to (from x) ≡ x
