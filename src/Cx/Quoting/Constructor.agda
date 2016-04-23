
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

module _ (`dt : Name) (#p : Nat) (I : Cx₀) where
  -- from: `p₀ , `p₁ , .. , `pn , `a₀ , `a₁ , .. , `an
  -- to:   (λ γ → tt , a₀ , a₁ , .. , an)
  indicesInCx : (offset : Nat) (Γ : Cx₁) → List (Arg Term) → TC (⟦ Γ ⟧ → ⟦ I ⟧)
  indicesInCx o Γ is = tryUnquoteTC "indicesInCx" $ termInCx o $
    foldl (con₂ (quote _▶₀_._,_)) (con₀ (quote ⊤′.tt)) $ map unArg $ drop #p is

  parseTarget : (offset : Nat) (Γ : Cx) → Term → TC (⟦ Γ ⟧ → ⟦ I ⟧)
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

    quoteConstructorFailsᵐ : (Γ : Cx) (`c : Name) → Tactic
    quoteConstructorFailsᵐ Γ `c = evalTC (ShouldFail (quoteConstructor Γ `c))


module _ where
  private
    data Dummy : Set where
      dZ : Dummy
      dS : Dummy → Dummy
      dHigh : (Bool → Dummy) → Dummy -- fails
      dWrapFin : (n : Nat) → Fin n → Dummy
      dStrengthen : (n : Nat) → Dummy → Fin n → Dummy

    testZ : quoteConstructorᵐ Dummy 0 ε ε dZ ≡ ι (λ γ → tt)
    testZ = refl

    testS : quoteConstructorᵐ Dummy 0 ε ε dS ≡ ("_" /rec (λ γ → tt) ⊗ ι (λ γ → tt))
    testS = refl

    testHigh : quoteConstructorFailsᵐ Dummy 0 ε ε dHigh
    testHigh = tt

    testWrapFin : quoteConstructorᵐ Dummy 0 ε ε dWrapFin
      ≡ ("n" / (λ _ → Nat) ⊗ "_" / (Fin ∘ top) ⊗ ι (λ _ → tt))
    testWrapFin = refl

    testStrengthen : quoteConstructorᵐ Dummy 0 ε ε dStrengthen
      ≡ ("n" / (λ _ → Nat) ⊗ "_" /rec (λ _ → tt) ⊗ "_" / (Fin ∘ top) ⊗ ι (λ _ → tt))
    testStrengthen = refl

    data DummyA (A : Set) : Set where
      dRec : A → DummyA A
      dOther : Dummy → DummyA A

    testRec : quoteConstructorᵐ DummyA 1 ε (ε ▷₁′ Set) dRec
      ≡ ("_" / (λ γ → top γ) ⊗ ι (λ γ → tt))
    testRec = refl

    testOther : quoteConstructorᵐ DummyA 1 ε (ε ▷₁′ Set) dOther
      ≡ ("_" / (λ γ → Dummy) ⊗ ι (λ γ → tt))
    testOther = refl

    data DummyAB (A B : Set) : Set where
      dPair : A → B → DummyAB A B

    testPair : quoteConstructorᵐ DummyAB 2 ε (ε ▷₁′ Set ▷₁′ Set) dPair
      ≡ ("_" / (top ∘ pop) ⊗ "_" / (top ∘ pop) ⊗ ι (λ γ → tt))
    testPair = refl

    data DummyN (A : Set) : Nat → Set where
      dNil : ∀ {n} → DummyN A n
      dCons : ∀ {n} → A → DummyN A n → DummyN A (suc n)

    testNil : quoteConstructorᵐ DummyN 1 (ε ▷ (λ γ → Nat)) (ε ▷₁′ Set) dNil
      ≡ ("n" / (λ γ → Nat) ⊗ ι (λ γ → tt , top γ))
    testNil = refl

    testCons : quoteConstructorᵐ DummyN 1 (ε ▷′ Nat) (ε ▷₁′ Set) dCons
      ≡ ("n" / (λ γ → Nat) ⊗ "_" / (λ γ → top (pop γ)) ⊗
         "_" /rec (λ γ → tt , top (pop γ)) ⊗ ι (λ γ → tt , suc (top (pop γ))))
    testCons = refl

    data DummyNB : (n : Nat) → Fin n → Set where
      dIFin : ∀ {n k} → DummyNB n k

    testIFin : quoteConstructorᵐ DummyNB 0 (ε ▷′ Nat ▷ (Fin ∘ top)) ε dIFin
      ≡ (("n" / (λ γ → Nat) ⊗ "k" / (Fin ∘ top) ⊗ ι (λ γ → (tt , top (pop γ)) , top γ)))
    testIFin = refl
