
module Cx.Quoting.Cx where

open import Common
open import Reflection
open import Tactic.Reflection
open import Cx.Cx

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
  substsVars′ : Nat → (Term → Term) → List SafeTerm → List SafeTerm
  substsVars′ zero f xs = xs
  substsVars′ (suc n) f xs = substsVars′ n (f ∘ `pop) (xs ++ [ safe (`top $ f $ var₀ 0) _ ])
substsVars : Nat → List SafeTerm
substsVars n = substsVars′ (suc n) id []

termInCx : Nat → Term → Term
termInCx n = lam visible ∘ abs "γ" ∘ substTerm (substsVars n)

private
  test-substsVars-0 : substsVars 0 ≡ safe (`top $ var₀ 0) _ ∷ []
  test-substsVars-0 = refl
  test-substsVars-2 : substsVars 2 ≡ (safe (`top $ var₀ 0) _ ∷
    safe (`top $ `pop $ var₀ 0) _ ∷ safe (`top $ `pop $ `pop $ var₀ 0 ) _ ∷ [])
  test-substsVars-2 = refl
  test-TermInCx : termInCx 2 (def₂ (quote Vec) (var₀ 2) (var₀ 0)) ≡
    lam visible (abs "γ" (def₂ (quote Vec) (`top $ `pop $ `pop $ var₀ 0) (`top $ var₀ 0)))
  test-TermInCx = refl


private
  -- Substitute variable references with tops and pops. Wrap each term in (λ γ →).
  wrapSubstVars′ : (Term → Term) → List SafeTerm → Telescope → List Term
  wrapSubstVars′ r rs [] = []
  wrapSubstVars′ r rs (arg _ x ∷ xs) = let rs′ = rs ++ [ safe (`top (r (var 0 []))) _ ] in
                                   lam visible (abs "γ" (substTerm rs′ x))
                                     ∷ wrapSubstVars′ (`pop ∘ r) rs′ xs
  wrapSubstVars : Telescope → List Term
  wrapSubstVars xs = wrapSubstVars′ id [] xs

  termListToCx : List Term → TC Cx
  termListToCx = foldl (λ x y → x >>= flip helper y) (return ε)
    where
    helper : Cx → Term → TC Cx
    helper tm x = catchTC (quoteTC tm >>=′ λ `tm → unquoteTC (`tm `▷ x)) $
                  catchTC (quoteTC tm >>=′ λ `tm → unquoteTC (`tm `▷₁ x)) $
                  typeError (strErr "Unsupported parameter" ∷ termErr x ∷ [])

paramCx : Nat → Type → TC Cx
paramCx #p = termListToCx ∘ wrapSubstVars ∘ take #p ∘ fst ∘ telView

module _ where
  private
    test-ty-2 : Set₁
    test-ty-2 = (A : Set) → (B : A → Set) → (n : Nat) → Vec A n → Bool
    test-paramCx-2a : evalT (paramCx 2 (quoteTerm test-ty-2)) ≡
      (ε ▷₁ (λ γ → Set) ▷₁ (λ γ → top γ → Set))
    test-paramCx-2a = refl
    test-paramCx-2b : evalT (paramCx 4 (quoteTerm test-ty-2)) ≡
      (ε ▷₁ (λ γ → Set) ▷₁ (λ γ → top γ → Set) ▷ (λ γ → Nat)
         ▷ (λ γ → Vec (top (pop (pop γ))) (top γ)))
    test-paramCx-2b = refl


--  -  -        1                2 1          3      2
-- {A} n → (x : A) → (xs : MyVec A n) → MyVec A (suc n)
--  0  1     2             3           str
--              1                2 1          2      1
-- n is hoeveel variabelen er beschikbaar zijn. var n komt overeen met top ∘ popⁿ

-- data MyVec (A : Set) : Nat → Set where
--   nil : MyVec A 0
--   cons : ∀ n → (x : A) → (xs : MyVec A n) → MyVec A (suc n)
-- a : {!strengthen 1 (def (quote Fin) (vArg (var 3 []) ∷ vArg (var 2 []) ∷ []))!}
-- a = {!strengthen 5 (quoteTerm (∀ {A} n → (x : A) → (xs : MyVec A n) → MyVec A (suc n)))!}

-- pi (hArg (agda-sort (lit 0)))
-- (abs "A"
--  (pi (vArg (def (quote Nat) []))
--   (abs "n"
--    (pi (vArg (var 1 []))
--     (abs "x"
--      (pi
--       (vArg (def (quote MyVec) (vArg (var 2 []) ∷ vArg (var 1 []) ∷ [])))
--       (abs "xs"
--        (def (quote MyVec)
--         (vArg (var 3 []) ∷
--          vArg (con (quote Nat.suc) (vArg (var 2 []) ∷ [])) ∷ [])))))))))
