module Desc.IsGood where

open import Data.Product
open import Data.Unit
open import Function

open import Desc.Desc

-- Show that _`×_ is redundant
-- Show that _`+_ and `1 can be implemented
-- Note that μ (internal fixpoints) are not implemented
-- Show that everything which can be created with `Σ can also be created with ×, +, 0, 1, ... . Probably not possible!



module Desc1 where
  -- As in Gentle Art of Levitation §3
  data Desc1 : Set₁ where
    `1 : Desc1
    `Σ : (S : Set) → (D : S → Desc1) → Desc1
    `ind× : (D : Desc1) → Desc1
    `hind× : (H : Set) → (D : Desc1) → Desc1
  
  ⟦_⟧1 : Desc1 → Set → Set
  ⟦_⟧1 `1 X = ⊤
  ⟦_⟧1 (`Σ S D) X = Σ[ s ∈ S ] (⟦ D s ⟧1 X)
  ⟦_⟧1 (`ind× D) X = X × ⟦ D ⟧1 X
  ⟦_⟧1 (`hind× H D) X = (H → X) × ⟦ D ⟧1 X

  upgrade : Desc1 → Desc
  upgrade `1 = `1
  upgrade (`Σ S D) = `Σ S λ s → upgrade (D s)
  upgrade (`ind× D) = `var `× upgrade D
  upgrade (`hind× H D) = (H `→ const `var) `× (upgrade D)

  open import Relation.Binary.PropositionalEquality
  open import Function.Inverse as FI using (_↔_)
  open import Function.Equality as FE using (_⟨$⟩_)

  -- The upgraded description interprets to an isomorphic pattern functor
  upgrade-⟦⟧ : ∀ D X → ⟦ D ⟧1 X ↔ ⟦ upgrade D ⟧ X
  upgrade-⟦⟧ `1 X = FI.id
  upgrade-⟦⟧ (`Σ S D) X = record
    { to = →-to-⟶ (λ { (x , d) → x , (to (upgrade-⟦⟧ (D x) X)) ⟨$⟩ d })
    ; from = →-to-⟶ (λ { (x , d) → x , _⟨$⟩_ (from (upgrade-⟦⟧ (D x) X)) d })
    ; inverse-of = record
      { left-inverse-of = λ { (x , d) → cong (_,_ x) (left-inverse-of (upgrade-⟦⟧ (D x) X) d) }
      ; right-inverse-of = λ { (x , d) → cong (_,_ x) (right-inverse-of (upgrade-⟦⟧ (D x) X) d) }
      }
    }
    where open FI.Inverse
  upgrade-⟦⟧ (`ind× D) X = record
    { to = →-to-⟶ (λ { (x , d) → x , to ⟨$⟩ d })
    ; from = →-to-⟶ (λ { (x , d) → x , from ⟨$⟩ d })
    ; inverse-of = record
      { left-inverse-of = λ { (x , d) → cong (_,_ x) (left-inverse-of d) }
      ; right-inverse-of = λ { (x , d) → cong (_,_ x) (right-inverse-of d) }
      }
    }
    where open FI.Inverse (upgrade-⟦⟧ D X)
  upgrade-⟦⟧ (`hind× H D) X = record
    { to = →-to-⟶ (λ { (x , d) → x , to ⟨$⟩ d })
    ; from = →-to-⟶ (λ { (x , d) → x , from ⟨$⟩ d })
    ; inverse-of = record
      { left-inverse-of = λ { (x , d) → cong (_,_ x) (left-inverse-of d) }
      ; right-inverse-of = λ { (x , d) → cong (_,_ x) (right-inverse-of d) }
      }
    }
    where open FI.Inverse (upgrade-⟦⟧ D X)

