
module Thesis.Extended where

open import Common
open import Cx.Extended hiding (⟦_⟧desc; fold)

{-# TERMINATING #-}
⟦_⟧desc : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → Pow ⟦ I ⟧ → Pow ⟦ I ⟧
⟦_⟧desc {dt = isCon} (ι o) γ X o′ = o γ ≡ o′
⟦_⟧desc {dt = isCon} (S ⊗ xs) γ X o = Σ (S γ) λ s → ⟦ xs ⟧desc (γ , s) X o
⟦_⟧desc {dt = isCon} (rec i ⊗ xs) γ X o = X (i γ) × ⟦ xs ⟧desc γ X o
⟦_⟧desc {dt = isDat #c} D γ X o = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧desc γ X o

{-# TERMINATING #-}
fold : ∀{I Γ #c}{D : DatDesc I Γ #c}{γ X} (α : Alg D γ X) →
       {i : ⟦ I ⟧} → μ D γ i → X i
fold {D = D} α ⟨ xs ⟩ = α (descmap (fold α) D xs)


--------------------
-- Example: specialising logins with parameters and give-K

postulate
  Uri Name Password : Set

loginDesc : DatDesc ε ε 1
loginDesc = const Uri ⊗ const Name ⊗ const Password ⊗ ι (λ γ → tt) ⊕ `0

getUri : μ loginDesc tt tt → Uri
getUri ⟨ zero , u , _ ⟩ = u
getUri ⟨ suc () , _ ⟩

postulate
  getLoginInfo : (u : Uri) → Σ (μ loginDesc tt tt) (λ li → getUri li ≡ u)

uriLoginDesc : DatDesc ε (ε ▷′ Uri) 1
uriLoginDesc = const Name ⊗ const Password ⊗ ι (λ γ → tt) ⊕ `0
login→uriLogin : DefOrn ε id (ε ▷′ Uri) (λ i → tt) loginDesc
login→uriLogin = (give-K (λ δ → top δ) $ -⊗ -⊗ ι (λ δ → inv tt)) ⊕ `0

uriLoginToLogin : ∀{u} → μ uriLoginDesc (tt , u) tt → μ loginDesc tt tt
uriLoginToLogin = forget login→uriLogin

postulate
  getLoginInfo′ : (u : Uri) → μ uriLoginDesc (tt , u) tt

module UriLoginInfoIsRefinement (u : Uri) where
  to : Σ (μ loginDesc tt tt) (λ li → getUri li ≡ u) →
       μ uriLoginDesc (tt , u) tt
  to (⟨ zero , _ , y ⟩ , _) = ⟨ 0 , y ⟩
  to (⟨ suc () , _ ⟩ , _)
  from : μ uriLoginDesc (tt , u) tt →
         Σ (μ loginDesc tt tt) (λ li → getUri li ≡ u)
  from ⟨ zero , y ⟩ = ⟨ 0 , u , y ⟩ , refl
  from ⟨ suc () , _ ⟩
  to-from : ∀ x → to (from x) ≡ x
  to-from ⟨ zero , _ ⟩ = refl
  to-from ⟨ suc () , _ ⟩
  from-to : ∀ x → from (to x) ≡ x
  from-to (⟨ zero , _ , _ ⟩ , eq) rewrite eq = refl
  from-to (⟨ suc () , _ ⟩ , _)

  iso : Iso (Σ (μ loginDesc tt tt) (λ li → getUri li ≡ u)) (μ uriLoginDesc (tt , u) tt)
  iso = record { to = to ; from = from ; to-from = to-from ; from-to = from-to }
