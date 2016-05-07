
module Cx.Cx.Reflection where

open import Common
open import Reflection
open import Stuff using (zipNats)
open import Cx.Cx.Core

`ε : Term
`ε = con₀ (quote ε)
_`▷_ : Term → Term → Term
t `▷ s = con₂ (quote _▷_) t s
_`▷₁_ : Term → Term → Term
t `▷₁ s = con₂ (quote _▷₁_) t s

`pop : Term → Term
`pop = def₁ (quote pop)
`top : Term → Term
`top = def₁ (quote top)


private
  substsVars : Nat → (Term → Term) → List SafeTerm → List SafeTerm
  substsVars zero f xs = xs
  substsVars (suc n) f xs = substsVars n (f ∘ `pop) (xs ++ [ safe (`top $ f $ var₀ 0) _ ])

-- Substitute variable references with tops and pops. Wrap the term in (λ γ →).
-- from: `(Ψ (var 0) (var 1) .. (var n))
-- to  : `(λ γ → Ψ (top γ) (pop $ top γ) .. (popⁿ $ top γ))
termInCx : Nat → Term → Term
termInCx n = lam visible ∘ abs "γ" ∘ substTerm (substsVars (suc n) id [])

private
  test-substsVars-0 : substsVars 1 id [] ≡ safe (`top $ var₀ 0) _ ∷ []
  test-substsVars-0 = refl
  test-substsVars-2 : substsVars 3 id [] ≡ (safe (`top $ var₀ 0) _ ∷
    safe (`top $ `pop $ var₀ 0) _ ∷ safe (`top $ `pop $ `pop $ var₀ 0 ) _ ∷ [])
  test-substsVars-2 = refl
  test-TermInCx : termInCx 2 (def₂ (quote Vec) (var₀ 2) (var₀ 0)) ≡
    lam visible (abs "γ" (def₂ (quote Vec) (`top $ `pop $ `pop $ var₀ 0) (`top $ var₀ 0)))
  test-TermInCx = refl


private
  termsInCxs : Telescope → List Term
  termsInCxs = zipNats λ { n (arg _ x) → termInCx n x }

  termListToCx : ∀{a} → List Term → TC (Cx {a})
  termListToCx = foldl (λ x y → x >>= flip helper y) (return ε)
    where
    helper : Cx → Term → TC Cx
    helper tm x = quoteTC tm >>=′ λ `tm →
                  catchTC (unquoteTC (`tm `▷ x)) $
                  catchTC (unquoteTC (`tm `▷₁ x)) $
                  typeError (strErr "The context" ∷ termErr `tm ∷
                             strErr "can not be extended with the term" ∷ termErr x ∷
                             strErr ".\nInvalid parameters or indices?" ∷ [])

typeToCx : ∀{a} (skip : Nat)(limit : Maybe Nat) → Type → TC (Cx {a})
typeToCx skip limit = termListToCx ∘ termsInCxs ∘
                      (maybe id take limit) ∘ drop skip ∘ fst ∘ telView

private
  macro
    typeToCxᵐ : {a : Level}(skip : Nat)(limit : Maybe Nat) → Type → Tactic
    typeToCxᵐ {a} skip limit ty = evalTC (typeToCx {a} skip limit ty)
    typeToCxFailsᵐ : {a : Level}(skip : Nat)(limit : Maybe Nat) → Type → Tactic
    typeToCxFailsᵐ {a} skip limit ty = evalTC (ShouldFail (typeToCx {a} skip limit ty))
  testty : Set₁
  testty = (A : Set) → (B : A → Set) → (n : Nat) → Vec A n → Set
  test-typeToCx-1 : typeToCxᵐ 0 (just 2) testty ≡
    (ε ▷₁ (λ γ → Set) ▷₁ (λ γ → top γ → Set))
  test-typeToCx-1 = refl
  test-typeToCx-2 : typeToCxᵐ 0 nothing testty ≡
    (ε ▷₁ (λ γ → Set) ▷₁ (λ γ → top γ → Set) ▷ (λ γ → Nat)
       ▷ (λ γ → Vec (top (pop (pop γ))) (top γ)))
  test-typeToCx-2 = refl
  test-typeToCx-3 : typeToCxᵐ {lzero} 2 (just 1) testty ≡
    (ε ▷′ Nat)
  test-typeToCx-3 = refl
  test-typeToCx-4 : typeToCxᵐ {lsuc lzero} 2 (just 1) testty ≡
    (ε ▷′ Nat)
  test-typeToCx-4 = refl

  test-typeToCx-5 : typeToCxFailsᵐ {lsuc lzero} 2 nothing testty
  test-typeToCx-5 = tt



-- Takes (ε ▷ p₁ ▷ p₂ ▷ .. ▷ pn) and `T
-- Returns `(∀{p₁ p₂ .. pn} → T)
cxType : ∀{a} → Cx {a} → Type → Type
cxType Γ ty = Cx-iter (pi (hArg unknown) ∘ abs "_") ty Γ

-- Takes an offset and (ε ▷ p₁ ▷ p₂ ▷ .. ▷ pn)
-- Returns [var (n+o) , .. , var (1+o) , var o]
cxVars : (offset : Nat) → ∀{a} → Cx {a} → List (Arg Term)
cxVars offset = let f = λ { (o , ts) → suc o , vArg (var₀ o) ∷ ts } in
                snd ∘ Cx-iter f (offset , [])

cxPats : ∀{a} → Cx {a} → List (Arg Pattern)
cxPats = Cx-iter (_∷_ (vArg (var "_"))) []

-- Takes an offset and (ε ▷ p₁ ▷ p₂ ▷ .. ▷ pn)
-- Returns `((((tt , var (n+o)) , ..) , var (1+o)) , var o)
cxVal : ∀ (offset : Nat) {a} → Cx {a} → Term
cxVal offset {a} = Cx-walk {Nat} {Term} offset suc suc (const (con₀ (quote ⊤′.tt)))
                           (λ n tm → con₂ (quote _▶₁_._,_) tm (`var₀ n ""))
                           (λ n tm → con₂ (quote _▶₀_._,_) tm (`var₀ n ""))

-- Takes a term and (ε ▷ S₁ ▷ S₂ ▷ .. ▷ Sn)
-- Returns _$_ {A = ⟦ ε ▷ S₁ ▷ S₂ ▷ .. ▷ Sn ⟧} `tm (((tt , vn) , .. , v2) , v1)
applyCx : ∀{a} → Cx {a} → (`γ `f : Term) → TC Term
applyCx {a} Γ `γ `f = _`$_ `f <$> forceTypeTC (⟦_⟧Cx {a} Γ) `γ


module CxToType where
  -- From (ε ▷₁ (λ γ → Set) ▷₁ (λ γ → top γ → Set) ▷ (λ γ → Nat)), cxToType builds something like this:
  --   (A : $A (⟦_⟧Cx {lsuc lzero} (ε))                                     (λ γ → Set) (tt)) →
  --   (B : $A (⟦_⟧Cx {lsuc lzero} (ε ▷₁′ Set))                              (λ γ → top γ → Set) (tt , A)) →
  --   (n : $A (⟦_⟧Cx {lsuc lzero} (ε ▷₁′ Set ▷₁ (λ γ → top γ → Set)))       (λ γ → Nat) ((tt , A) , B)) →
  --   Set
  -- Which is the same as:
  --   (A : Set) → (B : A → Set) → (C : Nat) → Set


  mutual
    cxToTel : ∀{a} → Cx {a} → TC Telescope
    cxToTel (Γ ▷₁ S) = quoteTC S >>= cxToTel-helper Γ
    cxToTel (Γ ▷ S) = quoteTC S >>= cxToTel-helper Γ
    cxToTel ε = return []

    cxToTel-helper : ∀{a} → Cx {a} → Term → TC Telescope
    cxToTel-helper {a} Γ `S =
      do xs ← cxToTel {a} Γ
      =| `tm ← applyCx Γ (cxVal 0 Γ) `S
      -| return (xs ++ [ vArg `tm ])

  cxToType : ∀{a} → Type → Cx {a} → TC Type
  cxToType {a} ty Γ = flip telPi ty <$> cxToTel {a} Γ

  Set→Cx→Set : ∀{a} → Set a → TC (Set a)
  Set→Cx→Set {a} x = ((quoteTC x >>=′ typeToCx {a} 0 nothing) >>=′ cxToType set₀) >>=′ unquoteTC

  test-Set₁→Cx→Set₁ : evalT (Set→Cx→Set testty) ≡ testty
  test-Set₁→Cx→Set₁ = refl

open CxToType using (cxToTel; cxToType) public
