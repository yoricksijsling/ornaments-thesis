
{-# OPTIONS --type-in-type #-}

module Thesis.Discussion where

open import Common

module ArgumentLanguage where
  module PolyP where
    -- Same as the codes in the introduction, but with |par|
    data Code : Set where
      ι : Code
      rec : Code
      par : Code
      _⊕_ : (F G : Code) → Code
      _⊗_ : (F G : Code) → Code

    ⟦_⟧code : Code → (P : Set) → (X : Set) → Set
    ⟦ ι ⟧code P X = ⊤
    ⟦ rec ⟧code P X = X
    ⟦ par ⟧code P X = P
    ⟦ A ⊕ B ⟧code P X = Either (⟦ A ⟧code P X) (⟦ B ⟧code P X)
    ⟦ A ⊗ B ⟧code P X = ⟦ A ⟧code P X × ⟦ B ⟧code P X

  module A where    

  open import Cx.Extended

  postulate
    flatten : ∀{A #c} (D : DatDesc ε (ε ▷₁′ Set) #c) →
      μ D (tt , A) tt → List A
    pmap : ∀{A B #c} (D : DatDesc ε (ε ▷₁′ Set) #c) →
      (f : A → B) → μ D (tt , A) tt → μ D (tt , B) tt
      
  isTop : (S : ⟦ ε ▷₁′ Set ⟧ → Set) → Dec (∀ γ → S γ ≡ top γ)
  isTop S = {!!}

  --------------------
  -- See DiscussionTermLang.agda for the universe with a language for
  -- arguments
  --------------------

