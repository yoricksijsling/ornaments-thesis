
-- Derive a HasDesc instance from a QuotedDesc

module Cx.HasDesc.Derive where

open import Common
open import Reflection

open import Cx.Named
open import Cx.HasDesc.Core

private
  `suc^ : ∀{tp} → Nat → ⟦ tp ⟧tp → ⟦ tp ⟧tp
  `suc^ zero x = x
  `suc^ (suc n) x = `con₁ (quote Fin.suc) (`suc^ n x)

  `natToFin : ∀{tp} → Nat → ⟦ tp ⟧tp
  `natToFin n = `suc^ n (`con₀ (quote Fin.zero))

  -- constructorᵢ x₁ ⋯ xn
  α : ∀{tp} → Name → List ⟦ tp ⟧tp → ⟦ tp ⟧tp
  α `con = `conₓ `con

  -- ⟨ sucⁱ zero , x₁ , ⋯ , xn , refl ⟩
  β : ∀{tp} → (i : Nat) → List ⟦ tp ⟧tp → ⟦ tp ⟧tp
  β i = `con₁ (quote ⟨_⟩) ∘ `con₂ (quote Σ._,_) (`natToFin i)
       ∘ foldr (`con₂ (quote Σ._,_)) (`con₀ (quote _≡_.refl))

  -- ⟨ sucⁱ () , _ ⟩
  absurd-β : (i : Nat) → Pattern
  absurd-β i = `con₁ (quote ⟨_⟩) $ `con₂ (quote Σ._,_) (`suc^ i absurd) (var "_")

  ΓIVars : (offset : Nat) → (Γ : Cx₁) → (I : Cx₀) → List (Arg Term)
  ΓIVars offset Γ I = cxVars (offset + CxLength I) Γ ++ cxVars offset I

  -- Takes a ConDesc (a ⊗ rec x ⊗ rec y ⊗ b ⊗ rec z ⊗ ι)
  -- Returns a list of patterns [a, x, y, b, z]
  patArgs : ∀{I Γ} → ConDesc I Γ → List Pattern
  patArgs (ι o) = []
  patArgs (nm / S ⊗ as) = var "" ∷ patArgs as
  patArgs (nm /rec i ⊗ as) = var "" ∷ patArgs as

  -- Takes a ConDesc (a ⊗ rec x ⊗ rec y ⊗ b ⊗ rec z ⊗ ι)
  -- Returns a list of terms [a, `f ps is x, `f ps is y, b, `f ps is z]
  termArgs : ∀{I Γ} → (`f : Name) → (offset : Nat) → ConDesc I Γ → List Term
  termArgs {I} {Γ} `f offset = snd ∘
    ConDesc-fold (0 , [])
                 (λ { (n , ts) → suc n , var₀ n ∷ ts })
                 (λ { (n , ts) → suc n , def₁ `f (var₀ n) ∷ ts})


module DeriveTo (`to : Name)(`desc : Term) where
  module _ (Γ : Cx₁)(I : Cx₀) where
    -- ∀{ps is} → `dt ps is → μ desc (tt , ps) (tt , is)
    type : (`dt : Name) → Type
    type `dt = cxType Γ $ cxType I $
               def `dt (ΓIVars 0 Γ I)
                 `→ def₃ (quote μ) `desc (cxVal (1 + CxLength I) Γ) (cxVal 1 I)

    -- to (con-α as) = con-β as
    makeClause : Nat → Name → ConDesc I Γ → Clause
    makeClause i `c D = clause [ vArg (α `c (patArgs D)) ]
                               (β i (termArgs `to (length (patArgs D)) D))

    makeClauses : ∀{#c} → Nat → (`cs : Vec Name #c) → DatDesc I Γ #c → List Clause
    makeClauses i [] `0 = []
    makeClauses i (`c ∷ `cs) (D ⊕ DS) = makeClause i `c D  ∷ makeClauses (suc i) `cs DS
  
  deriveTo : QuotedDesc Name → TC ⊤
  deriveTo (mk {I} {Γ} `datatypeName `constructorNames desc) =
    define (vArg `to) (type Γ I `datatypeName) (makeClauses Γ I 0 `constructorNames desc)

module DeriveFrom (`from : Name)(`desc : Term) where
  module _ (Γ : Cx₁) (I : Cx₀) where
    -- ∀{ps is} → μ desc (tt , ps) (tt , is) → `dt ps is
    type : (`dt : Name) → Type
    type `dt = cxType Γ $ cxType I $
               def₃ (quote μ) `desc (cxVal (CxLength I) Γ) (cxVal 0 I)
                 `→ def `dt (ΓIVars 1 Γ I)

    -- from (con-β as) = con-α as
    makeClause : Nat → Name → ConDesc I Γ → Clause
    makeClause i `c D = clause [ vArg (β i (patArgs D)) ]
                               (α `c (termArgs `from (length (patArgs D)) D))

    makeClauses : ∀{#c} → Nat → (`cs : Vec Name #c) → DatDesc I Γ #c → List Clause
    makeClauses i [] `0 = [ absurd-clause [ vArg (absurd-β i) ] ]
    makeClauses i (`c ∷ `cs) (D ⊕ DS) = makeClause i `c D ∷ makeClauses (suc i) `cs DS

  deriveFrom : QuotedDesc Name → TC ⊤
  deriveFrom (mk {I} {Γ} `datatypeName `constructorNames desc) =
    define (vArg `from) (type Γ I `datatypeName)
           (makeClauses Γ I 0 `constructorNames desc)

private
  -- ∀{ps is} → HasDesc (`dt ps is)
  hasDescType : QuotedDesc Name → Type
  hasDescType (mk {I} {Γ} `dt _ desc) = cxType Γ $ cxType I $
                                        def₁ (quote HasDesc) (def `dt (ΓIVars 0 Γ I))

  deriveHasDesc′ : (`hasDesc : Name) → (`desc : Term) → QuotedDesc Name → TC ⊤
  deriveHasDesc′ `hasDesc `desc q =
    do `to ← freshName "to"
    -| `from ← freshName "from"
    -| DeriveTo.deriveTo `to `desc q
    ~| DeriveFrom.deriveFrom `from `desc q
    ~| define (iArg `hasDesc) (hasDescType q)
              [ clause [] (con₃ (quote HasDesc.mk) `desc (def₀ `to) (def₀ `from)) ]


deriveHasDesc : (`quotedDesc `hasDesc `dt : Name) → TC ⊤
deriveHasDesc `quotedDesc `hasDesc `dt =
  do q ← quoteDatatype `dt
  =| `q ← quoteTC q
  -| define (vArg `quotedDesc) (quoteTerm (QuotedDesc Name))
            [ clause [] `q ]
  ~| `desc := def₁ (quote QuotedDesc.desc) (def₀ `quotedDesc)
  -| deriveHasDesc′ `hasDesc `desc q
  where open import Cx.Quoting
