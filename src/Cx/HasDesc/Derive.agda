
-- Derive a HasDesc instance from a QuotedDesc

module Cx.HasDesc.Derive where

open import Common
open import Reflection
-- open import Tactic.Reflection

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


  -- Takes (ε ▷ p₁ ▷ p₂ ▷ .. ▷ pn) and `T
  -- Returns `(∀{p₁ p₂ .. pn} → T)
  cxType : ∀{a} → Cx {a} → Type → Type
  cxType Γ ty = Cx-iter (pi (hArg unknown) ∘ abs "_") ty Γ

  -- Takes an offset and (ε ▷ p₁ ▷ p₂ ▷ .. ▷ pn)
  -- Returns [var (n+o) , .. , var (1+o) , var o]
  cxVars : (offset : Nat) → ∀{a} → Cx {a} → List (Arg Term)
  cxVars offset = let f = λ { (o , ts) → suc o , vArg (var₀ o) ∷ ts } in
                  snd ∘ Cx-iter f (offset , [])

  ΓIVars : (offset : Nat) → (Γ : Cx₁) → (I : Cx₀) → List (Arg Term)
  ΓIVars offset Γ I = cxVars (offset + CxLength I) Γ ++ cxVars offset I

  cxPats : ∀{a} → Cx {a} → List (Arg Pattern)
  cxPats = Cx-iter (_∷_ (vArg (var "_"))) []

  -- Takes an offset and (ε ▷ p₁ ▷ p₂ ▷ .. ▷ pn)
  -- Returns `((((tt , var (n+o)) , ..) , var (1+o)) , var o)
  cxVal : ∀ (offset : Nat) {a} → Cx {a} → Term
  cxVal offset = Cx-walk {Nat} {Term} offset suc suc (const (con₀ (quote ⊤′.tt)))
                         (λ n tm → con₂ (quote _▶₁_._,_) tm (`var₀ n ""))
                         (λ n tm → con₂ (quote _▶₀_._,_) tm (`var₀ n ""))

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
  
  deriveTo : QuotedDesc → TC ⊤
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

  deriveFrom : QuotedDesc → TC ⊤
  deriveFrom (mk {I} {Γ} `datatypeName `constructorNames desc) =
    define (vArg `from) (type Γ I `datatypeName)
           (makeClauses Γ I 0 `constructorNames desc)

-- ∀{ps is} → HasDesc (`dt ps is)
hasDescType : QuotedDesc → Type
hasDescType (mk {I} {Γ} `dt _ desc) = cxType Γ $ cxType I $
                                      def₁ (quote HasDesc) (def `dt (ΓIVars 0 Γ I))

deriveHasDesc : (`hasDesc : Name) → QuotedDesc → TC ⊤
deriveHasDesc `hasDesc q =
  do `q ← quoteTC q
  -| let `desc = def₁ (quote QuotedDesc.desc) `q in
     `to ← freshName "to"
  -| `from ← freshName "from"
  -| DeriveTo.deriveTo `to `desc q
  ~| DeriveFrom.deriveFrom `from `desc q
  ~| define (iArg `hasDesc) (hasDescType q)
            [ clause [] (con₃ (quote HasDesc.mk) `q (def₀ `to) (def₀ `from)) ]
