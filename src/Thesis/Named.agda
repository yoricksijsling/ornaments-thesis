
module Thesis.Named where

open import Common hiding (Vec; List; Fin)
open import Reflection
open import Cx.HasDesc hiding (fold)
open import Cx.Unquoting


data Vec (A : Set) : Nat → Set where
  nil : Vec A 0
  cons : ∀ n → (x : A) → (xs : Vec A n) → Vec A (suc n)

-- Quote the |Vec| datatype
unquoteDecl quotedVec VecHasDesc =
  deriveHasDesc quotedVec VecHasDesc (quote Vec)

-- Two new functions have been defined:
-- quotedVec : QuotedDesc
-- VecHasDesc : {A : Set} {n : Nat} → HasDesc (Vec A n)


----------------------------------------
-- Descriptions and ornaments

vecDesc : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
vecDesc = ι (const (tt , 0))
  ⊕ "n" / const Nat ⊗
    "x" / top ∘ pop ⊗
    "xs" /rec (λ γ → tt , top (pop γ)) ⊗
    ι (λ γ → tt , suc (top (pop γ)))
  ⊕ `0


----------------------------------------
-- Quoting

quotedVec-check : quotedVec ≡
  mk (quote Vec) (quote Vec.nil ∷ quote Vec.cons ∷ []) vecDesc
quotedVec-check = refl

vecDesc-check : QuotedDesc.desc quotedVec ≡ vecDesc
vecDesc-check = refl


----------------------------------------
-- Deriving

postulate instance VecHasDesc′ : ∀{A n} → HasDesc (Vec A n)

vec-to : ∀{A n} → Vec A n → μ vecDesc (tt , A) (tt , n)
vec-to = to
vec-from : ∀{A n} → μ vecDesc (tt , A) (tt , n) → Vec A n
vec-from = from


----------------------------------------
-- Generic functions

{-# TERMINATING #-}
-- fold : ∀{I Γ #c}{D : DatDesc I Γ #c}{γ X}
--   (α : Alg D γ X) → μ D γ →ⁱ X
fold : ∀{I Γ #c γ i}{D : DatDesc I Γ #c} → ∀{X} →
  (α : Alg D γ X) → μ D γ i → X i
fold {D = D} α ⟨ xs ⟩ = α (descmap (fold α) D xs)

module _ where
  open HasDesc

  gfold : ∀{A}⦃ _R : HasDesc A ⦄ → ∀{X} →
    Alg (desc _R) (γ _R) X → A → X (i _R)
  gfold α = fold α ∘ to


vecSumAlg : Alg vecDesc (tt , Nat) (λ i → Nat)
vecSumAlg (zero , refl) = 0
vecSumAlg (suc zero , _ , x , sum , refl) = x + sum
vecSumAlg (suc (suc ()) , y)

vec-example : Vec Nat 4
vec-example = cons _ 3 (cons _ 1 (cons _ 5 (cons _ 6 nil)))

vec-example-sum : gfold vecSumAlg vec-example ≡ 15
vec-example-sum = refl

----

-- Does not work when A has parameters..

module _ where
  open HasDesc

  gforget : ∀{A}⦃ _AR : HasDesc A ⦄{B}⦃ _BR : HasDesc B ⦄ →
    ∀{u c} (o : Orn (I _BR) u (Γ _BR) c (desc _AR)) →
    ⦃ ieq : i _AR ≡ u (i _BR) ⦄
    ⦃ γeq : γ _AR ≡ c (γ _BR) ⦄
    ⦃ #ceq : #c _AR ≡ #c _BR ⦄
    ⦃ deq : transport (DatDesc (I _BR) (Γ _BR)) #ceq (ornToDesc o)
      ≡ desc _BR ⦄ →
    B → A
  gforget ⦃ _AR = mk desc Ato Afrom ⦄
    ⦃ _BR = mk .(ornToDesc o) Bto Bfrom ⦄ o
    ⦃ refl ⦄ ⦃ refl ⦄ ⦃ refl ⦄ ⦃ refl ⦄ = Afrom ∘ forget o ∘ Bto


data List (A : Set) : Set where
  [] : List A
  _∷_ : (x : A) → (xs : List A) → List A

unquoteDecl quotedList ListHasDesc =
  deriveHasDesc quotedList ListHasDesc (quote List)

listDesc : DatDesc ε (ε ▷₁′ Set) 2
listDesc = QuotedDesc.desc quotedList

list→vec : Orn (ε ▷′ Nat) (λ i → tt) (ε ▷₁′ Set) id listDesc
list→vec = ι (λ δ → inv (tt , 0))
  ⊕ "n" / const Nat +⊗
     "x" /-⊗
     "xs" /rec (λ δ → inv (tt , top (pop δ))) ⊗
     ι (λ δ → inv (tt , suc (top (pop δ))))
  ⊕ `0

vec-example-forget : gforget list→vec vec-example ≡
  (3 ∷ 1 ∷ 5 ∷ 6 ∷ [] ofType List Nat)
vec-example-forget = refl


----------------------------------------
-- Unquoting

unquoteDecl quotedNat NatHasDesc =
  deriveHasDesc quotedNat NatHasDesc (quote Nat)

natDesc : DatDesc ε ε 2
natDesc = QuotedDesc.desc quotedNat

nat→fin : Orn (ε ▷′ Nat) (λ i → tt) ε id natDesc
nat→fin = "n" / const Nat +⊗ ι (λ δ → inv (tt , suc (top δ)))
  ⊕ "n" / const Nat +⊗ "_" /rec (λ δ → inv (tt , top δ)) ⊗ ι (λ δ → inv (tt , suc (top δ)))
  ⊕ `0

finDesc : DatDesc (ε ▷′ Nat) ε 2
finDesc = ornToDesc nat→fin

data Fin : unquoteDat finDesc where
  zero : unquoteCon finDesc 0 Fin
  suc : unquoteCon finDesc 1 Fin

unquoteDecl quotedFin FinHasDesc =
  deriveHasDescExisting quotedFin FinHasDesc
  (quote Fin) finDesc

fin-to-nat : ∀{n} → Fin n → Nat
fin-to-nat = gforget nat→fin

----------------------------------------
-- Building more ornaments


nat→list : Orn ε id (ε ▷₁′ Set) (λ _ → tt) natDesc
nat→list = ι (λ δ → inv tt)
  ⊕ "x" / top +⊗
    "xs" /rec (λ δ → inv tt) ⊗
    ι (λ δ → inv tt)
  ⊕ `0

nat→list′ : Orn _ _ _ _ natDesc
nat→list′ = renameArguments 1 (just "xs" ∷ [])
  >>⁺ addParameterArg 1 "x"

nat→list″ : Orn ε id (ε ▷₁′ Set) (λ _ → tt) natDesc
nat→list″ = reparam
  ⊕ "x" / top +⊗
  (reparam >>⁺ conRenameArguments (just "xs" ∷ []))
  ⊕ `0

list-rename₁ : Orn ε id (ε ▷₁′ Set) id listDesc
list-rename₁ = ι (λ δ → inv tt)
  ⊕ "y" /-⊗
    "ys" /rec (λ δ → inv tt) ⊗
    ι (λ δ → inv tt)
  ⊕ `0

--------------------
-- Reornament

{-
postulate
  reornament′ : ∀{I J u Δ Γ}{c : Cxf Δ Γ}{#c}{D : DatDesc I Γ #c} →
    (o : Orn J u Δ c D) → Orn (J ▷ μ D (c {!!}) ∘ u) (u ∘ pop) Δ c D
-}

natDesc′ : DatDesc ε ε 2
natDesc′ = natDesc
natDesc-zero : μ natDesc tt tt
natDesc-zero = ⟨ 0 , refl ⟩
natDesc-suc : μ natDesc tt tt → μ natDesc tt tt
natDesc-suc n = ⟨ 1 , n , refl ⟩

-- nat→list : Orn ε id (ε ▷₁′ Set) (λ δ → tt) natDesc
-- nat→list = ι (λ δ → inv tt)
--   ⊕ top +⊗ rec (λ δ → inv tt) ⊗ ι (λ δ → inv tt)
--   ⊕ `0

nat→vecᵣ : Orn (ε ▷′ μ natDesc tt tt) (λ j → tt) (ε ▷₁′ Set) (λ δ → tt) natDesc
nat→vecᵣ = reornament nat→list

vecDescᵣ : DatDesc (ε ▷′ μ natDesc tt tt) (ε ▷₁′ Set) 2
vecDescᵣ = ι (const (tt , natDesc-zero))
  ⊕ "x" / top
  ⊗ "_" / const (μ natDesc tt tt)
  ⊗ "xs" /rec (λ γ → tt , top γ)
  ⊗ ι (λ γ → tt , natDesc-suc (top γ))
  ⊕ `0

test-nat→vec : ornToDesc nat→vecᵣ ≡ vecDescᵣ
test-nat→vec = refl


----------------------------------------
-- Discussion


vec-example-rep : μ vecDesc (tt , Nat) (tt , 4)
vec-example-rep = to vec-example

vec-example′ : Vec Nat 4
vec-example′ = from vec-example-rep


module BetterStructure where
  -- Problem: type of |gforget list→vec vec-example| can not be
  -- inferred if |A| contains parameters. Solution: Lookup of
  -- embedding-projection pairs goes by type now, but should also be
  -- possible by desc
  record EmbeddingProjection (A : Set) {I Γ #c}
    (desc : DatDesc I Γ #c) (γ : ⟦ Γ ⟧) (i : ⟦ I ⟧) : Set₂ where
    constructor mk
    field
      to′ : A → μ desc γ i
      from′ : μ desc γ i → A

  record Embeddable (A : Set) : Set₂ where
    constructor mk
    field
      {I Γ} : Cx
      {#c} : Nat
      desc : DatDesc I Γ #c
      γ : ⟦ Γ ⟧
      i : ⟦ I ⟧
      ep : EmbeddingProjection A desc γ i

  record Projectable {I Γ #c}
    (desc : DatDesc I Γ #c) (γ : ⟦ Γ ⟧) (i : ⟦ I ⟧) : Set₂ where
    constructor mk
    field
      A : Set
      ep : EmbeddingProjection A desc γ i

  open EmbeddingProjection
  open Embeddable
  open Projectable

  to″ : ∀{A}⦃ _R : Embeddable A ⦄ → A → μ (desc _R) (γ _R) (i _R)
  to″ ⦃ mk desc γ i ep ⦄ = to′ ep

  from″ : ∀{I Γ #c desc γ i}⦃ _R : Projectable {I} {Γ} {#c} desc γ i ⦄ →
    μ desc γ i → A _R
  from″ ⦃ mk A ep ⦄ = from′ ep

  gfold′ : ∀{A}⦃ _R : Embeddable A ⦄ → ∀{X} →
    Alg (desc _R) (γ _R) X → A → X (i _R)
  gfold′ α = fold α ∘ to″

  gforget′ : ∀{B}⦃ _BR : Embeddable B ⦄ →
    ∀{AI AΓ Adesc u c} (o : Orn {AI} (I _BR) u {AΓ} (Γ _BR) c Adesc) →
    ⦃ deq : ornToDesc o ≡ desc _BR ⦄ →
    ⦃ _AR : Projectable Adesc (c (γ _BR)) (u (i _BR)) ⦄ →
    B → A _AR
  gforget′ ⦃ mk Bdesc Bγ Bi Bep ⦄ o ⦃ deq ⦄ ⦃ mk A Aep ⦄ =
    from′ Aep ∘ forget o ∘ transport (λ d → μ d Bγ Bi) (sym deq) ∘ to′ Bep
