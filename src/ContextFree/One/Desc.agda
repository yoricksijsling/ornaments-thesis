module ContextFree.One.Desc where

open import Common

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
⟦_⟧ (A `+ B) X = Either (⟦ A ⟧ X) (⟦ B ⟧ X)
⟦_⟧ (A `* B) X = ⟦ A ⟧ X × ⟦ B ⟧ X
⟦_⟧ `var X = X

data μ (D : Desc) : Set where
  ⟨_⟩ : ⟦ D ⟧ (μ D) → μ D

instance
  ⟦⟧-functor : ∀ D → Functor ⟦ D ⟧
  ⟦⟧-functor (`P₀ S) = record { fmap = λ f x → x }
  ⟦⟧-functor `0 = record { fmap = λ f x → x }
  ⟦⟧-functor `1 = record { fmap = λ f x → x }
  ⟦⟧-functor (A `+ B) = record { fmap = λ f → mapEither (fmap {{⟦⟧-functor A}} f) (fmap {{⟦⟧-functor B}} f) }
  ⟦⟧-functor (A `* B) = record { fmap = λ f → map× (fmap f) (fmap f) }
  ⟦⟧-functor `var = record { fmap = λ f → f }

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
