
module Cx.Conversions where

open import Common
import Cx.Simple as S
import Cx.Extended as E
import Cx.Named as N


module Simple↔Named where
  open N
  
  -- toSimple is not entirely reversible, because names are lost.
  private
    conToSimple : ∀{Γ} → ConDesc ε Γ → S.ConDesc Γ
    conToSimple (ι _) = S.ι
    conToSimple (_ / S ⊗ xs) = S S.⊗ conToSimple xs
    conToSimple (_ /rec _ ⊗ xs) = S.rec-⊗ (conToSimple xs)
  toSimple : ∀{#c} → DatDesc ε ε #c → S.DatDesc #c
  toSimple `0 = S.`0
  toSimple (x ⊕ xs) = conToSimple x S.⊕ toSimple xs

  private
    conToNamed : ∀{Γ} → S.ConDesc Γ → ConDesc ε Γ
    conToNamed S.ι = ι (λ _ → tt)
    conToNamed (S S.⊗ xs) = "_" / S ⊗ conToNamed xs
    conToNamed (S.rec-⊗ xs) = "_" /rec (λ _ → tt) ⊗ conToNamed xs
  toNamed : ∀{#c} → S.DatDesc #c → DatDesc ε ε #c
  toNamed S.`0 = `0
  toNamed (x S.⊕ xs) = conToNamed x ⊕ toNamed xs

module Extended↔Named where
  open N

  -- toExtended is not entirely reversible, because names are lost.
  private
    conToExtended : ∀{I Γ} → ConDesc I Γ → E.ConDesc I Γ
    conToExtended (ι o) = E.ι o
    conToExtended (_ / S ⊗ xs) = S E.⊗ conToExtended xs
    conToExtended (_ /rec i ⊗ xs) = E.rec i ⊗ (conToExtended xs)
  toExtended : ∀{I Γ #c} → DatDesc I Γ #c → E.DatDesc I Γ #c
  toExtended `0 = E.`0
  toExtended (x ⊕ xs) = conToExtended x E.⊕ toExtended xs

  private
    conToNamed : ∀{I Γ} → E.ConDesc I Γ → ConDesc I Γ
    conToNamed (E.ι o) = ι o
    conToNamed (S E.⊗ xs) = "_" / S ⊗ conToNamed xs
    conToNamed (E.rec i ⊗ xs) = "_" /rec i ⊗ conToNamed xs
  toNamed : ∀{I Γ #c} → E.DatDesc I Γ #c → DatDesc I Γ #c
  toNamed E.`0 = `0
  toNamed (x E.⊕ xs) = conToNamed x ⊕ toNamed xs

  -- Equal except names
  _≡ⁿ_ : ∀{I Γ dt} → (X Y : Desc I Γ dt) → Set₁
  _≡ⁿ_ {dt = isCon} X Y = conToExtended X ≡ conToExtended Y
  _≡ⁿ_ {dt = isDat #c} X Y = toExtended X ≡ toExtended Y

open Extended↔Named using (_≡ⁿ_) public
