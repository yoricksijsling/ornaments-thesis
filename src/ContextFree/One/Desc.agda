module ContextFree.One.Desc where

open import Data.Empty
open import Data.Unit.Base
open import Data.Sum
open import Data.Product

infixr 3 _`+_
infixr 4 _`*_

-- One variable, not dependently typed
data Desc : Set₁ where
  `P₀ : (S : Set₀) → Desc
  `0 : Desc
  `1 : Desc
  _`+_ : (A B : Desc) → Desc
  _`*_ : (A B : Desc) → Desc
  `var : Desc

⟦_⟧ : Desc → Set → Set
⟦_⟧ (`P₀ S) X = S
⟦_⟧ `0 X = ⊥
⟦_⟧ `1 X = ⊤
⟦_⟧ (A `+ B) X = ⟦ A ⟧ X ⊎ ⟦ B ⟧ X
⟦_⟧ (A `* B) X = ⟦ A ⟧ X × ⟦ B ⟧ X
⟦_⟧ `var X = X

data μ (D : Desc) : Set where
  ⟨_⟩ : ⟦ D ⟧ (μ D) → μ D

open import Category.Functor
open RawFunctor
⟦⟧-functor : ∀ D → RawFunctor ⟦ D ⟧
⟦⟧-functor `0 = record { _<$>_ = λ f x → x }
⟦⟧-functor `1 = record { _<$>_ = λ f x → x }
⟦⟧-functor (`P₀ S) = record { _<$>_ = λ f x → x }
⟦⟧-functor (A `+ B) = record { _<$>_ = λ f → Data.Sum.map (_<$>_ (⟦⟧-functor A) f)
                                                          (_<$>_ (⟦⟧-functor B) f) }
⟦⟧-functor (A `* B) = record { _<$>_ = λ f → Data.Product.map (_<$>_ (⟦⟧-functor A) f)
                                                              (_<$>_ (⟦⟧-functor B) f) }
⟦⟧-functor `var = record { _<$>_ = λ f → f }

open import Relation.Binary.PropositionalEquality using (_≡_)

record RawIsContextFree (A : Set) : Set₁ where
  constructor mk
  field
    desc : Desc
    to : A → μ desc
    from : μ desc → A

record IsContextFree (A : Set) : Set₁ where
  constructor mk
  field
    desc : Desc
    to : A → μ desc
    from : μ desc → A
    to-from : ∀ x → from (to x) ≡ x
    from-to : ∀ x → to (from x) ≡ x
