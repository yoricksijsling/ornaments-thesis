
module Cx.Quoting.Constructor where

open import Container.Traversable
open import Tactic.Reflection

open import Common
open import Reflection
open import Cx.Named
open import Cx.Quoting.Cx

instance
  DeBruijnAbs : {A : Set} {{_ : DeBruijn A}} → DeBruijn (Abs A)
  DeBruijnAbs = DeBruijnTraversable

module _ (`dt : Name) (#p : Nat) (I : Set) where
  -- May be wrong for multiple indices?
  indicesInCx : (offset : Nat) (Γ : Cx) → List (Arg Term) → TC (⟦ Γ ⟧ → I)
  indicesInCx o Γ is = tryUnquoteTC "indicesInCx" $ termInCx o $
    foldr (con₂ (quote Σ._,_)) (con₀ (quote ⊤.tt)) $ map unArg $ drop #p is

  parseTarget : (offset : Nat) (Γ : Cx) → Term → TC (⟦ Γ ⟧ → I)
  parseTarget o Γ (def `f args) with `f == `dt
  parseTarget o Γ (def _ args) | yes _ = indicesInCx o Γ args
  parseTarget o Γ (def `f args) | no _ = typeError $
    strErr "parseTarget: Invalid constructor target" ∷ termErr (def `f args) ∷ []
  parseTarget o Γ tm = typeError $
    strErr "parseTarget: Invalid constructor target" ∷ termErr tm ∷ []
  
  data ShapeView : Abs (Arg Term) → Set where
    shape-rec : ∀ s i args → ShapeView (abs s (arg i (def `dt args)))
    shape-⊗ : ∀ s i tm → ShapeView (abs s (arg i tm))
    shape-fail : ∀ s i tm → String → ShapeView (abs s (arg i tm))

  shapeView : (tm : Abs (Arg Term)) → ShapeView tm
  shapeView (abs s (arg i tm)) with absTelView tm
  shapeView (abs s (arg i _)) | ttel  , def `f args , refl with `f == `dt
  shapeView (abs s (arg i _)) | []    , def `f args , refl | yes p rewrite p = shape-rec s i args
  shapeView (abs s (arg i _)) | _ ∷ _ , def `f args , refl | yes p = shape-fail s i _ "Π-types are not supported"
  shapeView (abs s (arg i _)) | ttel  , def `f args , refl | no ¬p = shape-⊗ s i _
  shapeView (abs s (arg i _)) | ttel  , ttarget , refl = shape-⊗ s i _
    
  {-# TERMINATING #-}
  parseConstructor : (offset : Nat) (Γ : Cx) (ctel : AbsTelescope) (ctarget : Type) → TC (ConDesc I Γ)
  parseConstructor o Γ [] ctarget = ι <$> parseTarget o Γ ctarget
  parseConstructor o Γ (tm ∷ ctel) ctarget with shapeView tm
  parseConstructor o Γ (_ ∷ ctel) ctarget | shape-rec s i args =
    do is ← indicesInCx o Γ args
    =| stel ← fromMaybe "Can't strengthen telescope" (strengthen 1 ctel)
    =| starget ← fromMaybe "Can't strengthen target" (strengthen 1 ctarget)
    =| rest ← parseConstructor o Γ stel starget
    =| return (s /rec is ⊗ rest)
  parseConstructor o Γ (_ ∷ ctel) ctarget | shape-⊗ s i tm =
    do tm′ ← tryUnquoteTC "termInCx" (termInCx o tm)
    =| rest ← parseConstructor (suc o) (Γ ▷ tm′) ctel ctarget
    =| return (s / tm′ ⊗ rest)
  parseConstructor o Γ (_ ∷ ctel) ctarget | shape-fail s i tm msg = typeError $
    strErr "Failed to parse constructor argument (" ∷ strErr s ∷ strErr ":" ∷ termErr tm ∷ strErr ")." ∷
    strErr msg ∷ []

  quoteConstructor : (Γ : Cx) (`c : Name) → TC (ConDesc I Γ)
  quoteConstructor Γ `c =
    do cty ← getType `c
    =| let tel×target = absTelescope cty in
       parseConstructor #p Γ (drop #p (fst tel×target)) (snd tel×target)

  macro
    quoteConstructorᵐ : (Γ : Cx) (`c : Name) → Tactic
    quoteConstructorᵐ Γ `c = evalTC (quoteConstructor Γ `c)

    maybeQuoteConstructorᵐ : (Γ : Cx) (`c : Name) → Tactic
    maybeQuoteConstructorᵐ Γ `c = evalTC $ catchTC (quoteConstructor Γ `c >>= return ∘ just)
                                                   (return nothing)

module _ where
  private
    data Dummy : Set where
      dZ : Dummy
      dS : Dummy → Dummy

    testZ : quoteConstructorᵐ Dummy 0 ⊤ ε dZ ≡ ι (λ γ → tt)
    testZ = refl

    testS : quoteConstructorᵐ Dummy 0 ⊤ ε dS ≡ ("_" /rec (λ γ → tt) ⊗ ι (λ γ → tt))
    testS = refl

    data Dummy2 (A : Set) : Set where
      dRec : A → Dummy2 A
      dOther : Dummy → Dummy2 A

    testRec : quoteConstructorᵐ Dummy2 1 ⊤ (ε ▷₁ (const Set)) dRec
              ≡ ("_" / (λ γ → top γ) ⊗ ι (λ γ → tt))
    testRec = refl

    testOther : quoteConstructorᵐ Dummy2 1 ⊤ (ε ▷₁ (const Set)) dOther
                ≡ ("_" / (λ γ → Dummy) ⊗ ι (λ γ → tt))
    testOther = refl

    data Dummy3 (A B : Set) : Set where
      dPair : A → B → Dummy3 A B

    testPair : quoteConstructorᵐ Dummy3 2 ⊤ (ε ▷₁ (const Set) ▷₁ (const Set)) dPair
               ≡ ("_" / (top ∘ pop) ⊗
                  "_" / (top ∘ pop) ⊗ ι (λ γ → tt))
    testPair = refl


    data DummyF : Set where
      dHigh : (Bool → DummyF) → DummyF

    testHigh : maybeQuoteConstructorᵐ DummyF 0 ⊤ ε dHigh ≡ nothing
    testHigh = refl
