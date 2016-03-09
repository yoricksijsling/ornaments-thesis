module ContextFree.Multi.Quotable.Define where

open import Common
open import ContextFree.Multi.Desc
open import ContextFree.Multi.Params
open import ContextFree.Multi.Quotable.Core
open import ContextFree.Multi.Quoted
open import Reflection
open import Stuff using (zipNats; zipNatsDown)
open import Builtin.Size using (ω)

private
  right^_ : ∀{tp} → Nat → ⟦ tp ⟧tp → ⟦ tp ⟧tp
  right^_ zero = id
  right^_ (suc n) = `con₁ (quote right) ∘ (right^ n)

module AlphaBeta where
  -- constructorᵢ x₁ ⋯ xn
  α : ∀{tp} → Name → List ⟦ tp ⟧tp → ⟦ tp ⟧tp
  α `con = `conₓ `con

  -- ⟨ inj₂ⁱ (inj₁ (x₁ , ⋯ , xn , tt)) ⟩
  β : ∀{tp} → (i : Nat) → List ⟦ tp ⟧tp → ⟦ tp ⟧tp
  β i = `con₁ (quote ⟨_⟩) ∘ right^ i ∘ `con₁ (quote left)
       ∘ foldr (`con₂ (quote _,_)) (`con₀ (quote ⊤.tt))

module ToFrom {pc : Nat}(params : Vec Param pc) where
  -- Given a list of arguments [a, x, y, b, z], where xyz are recursive arguments
  -- Returns a list of patterns [a, x, y, b, z]
  patArgs : List (SafeArg {pc}) → List Pattern
  patArgs as = zipNatsDown 0 (λ meᵢ a → `var₀ meᵢ "") as

  -- Given a list of arguments [a, x, y, b, z], where xyz are recursive arguments
  -- Returns a list of terms [a, `f x, `f y, b, `f z]
  termArgs : (`f : Name) → List (SafeArg {pc}) → List Term
  termArgs `f as = zipNatsDown 0 termArg as
    where
    termArg : Nat → SafeArg {pc} → Term
    termArg meᵢ (Spar i) = `var₀ meᵢ ""
    termArg meᵢ Srec = def `f (paramVars (length as) params ++ [ vArg (`var₀ meᵢ "") ])

module Req (`req `desc : Name) where
  module WithParams {pc : Nat}(params : Vec Param pc) where
    open ToFrom params

    suc^_ : Nat → Pattern → Pattern
    suc^_ zero = id
    suc^_ (suc n) = `con₁ (quote Fin.suc) ∘ (suc^ n)

    makeClause : Nat → ⊤ → Clause
    makeClause i tt =
      clause (paramPats params ++ [ vArg (suc^ i $ `con₀ (quote Fin.zero)) ])
             (var (pc - (suc i)) [])

    makeClauses : List Clause
    makeClauses = zipNats makeClause (replicate pc tt) ++
                  [ absurd-clause (paramPats params ++ [ vArg (suc^ pc $ absurd) ]) ]

    type : Type
    type = addParams (vecToList params) $
           `def₁ (quote ISet)
                 (`def₁ (quote Fin)
                        (lit (nat pc)))

  defineReq : NamedSafeDatatype → TC ⊤
  defineReq (mk `dt params indices sop) = define (vArg `req) type makeClauses
    where open WithParams params

module To (`to `desc `req : Name) where
  module WithParams {pc : Nat}(params : Vec Param pc) where
    open AlphaBeta
    open ToFrom params

    makeClause : Nat → Named {SafeProduct {pc}} → Clause
    makeClause i (`con , as) = clause (paramPats params ++ [ vArg (α `con $ patArgs as) ])
                                      (β i $ termArgs `to as)

    makeClauses : Named {SafeSum {pc}} → List Clause
    makeClauses = zipNats makeClause

    type : (`dt : Name) → Type
    type `dt = addParams (vecToList params) $
               def `dt (paramVars 0 params)
                 `→ `def₃ (quote ⟦_⟧)
                          (`def₀ `desc)
                          (def `req (paramVars 1 params))
                          (`con₀ (quote ⊤.tt))

  defineTo : NamedSafeDatatype → TC ⊤
  defineTo (mk `dt params indices sop) = define (vArg `to) (type `dt) (makeClauses sop)
    where open WithParams params

module From (`from `desc `req : Name) where
  module WithParams {pc : Nat}(params : Vec Param pc) where
    open AlphaBeta
    open ToFrom params

    α-term : Named {SafeProduct {pc}} → Term
    α-term (`con , as) = α `con (termArgs `from as)

    β-pattern : Nat → Named {SafeProduct {pc}} → Pattern
    β-pattern i (`con , as) = β i (patArgs as)

    β-last : Nat → Pattern
    β-last n = `con₁ (quote ⟨_⟩) ((right^ n) absurd)

    makeClause : Nat → Named {SafeProduct {pc}} → Clause
    makeClause i (`con , as) = clause (paramPats params ++ [ vArg (β i $ patArgs as) ])
                                      (α `con $ termArgs `from as)

    makeClauses : Named {SafeSum {pc}} → List Clause
    makeClauses ps = zipNats makeClause ps
                   ++ [ absurd-clause (paramPats params ++ [ vArg (β-last (length ps)) ]) ]

    type : (`dt : Name) → Type
    type `dt = addParams (vecToList params) $
               def (quote ⟦_⟧)
                   ( vArg (`def₀ `desc)
                   ∷ hArg (`def₀ (quote ω))
                   ∷ vArg (def `req (paramVars 0 params))
                   ∷ vArg (`con₀ (quote ⊤.tt))
                   ∷ [])
                 `→ def `dt (paramVars 1 params)

  defineFrom : NamedSafeDatatype → TC ⊤
  defineFrom (mk `dt params indices sop) = define (vArg `from) (type `dt) (makeClauses sop)
    where open WithParams params

module Record (`record `desc `to `from : Name) where
  module WithParams {pc : Nat}(params : Vec Param pc) where
    type : (`dt : Name) → Type
    type `dt = addParams (vecToList params) $
               `def₁ (quote RawQuotable) (def `dt (paramVars 0 params))

    makeClauses : List Clause
    makeClauses = [_] $ clause (paramPats params) $
                  `con₃ (quote RawQuotable.mk) (def `desc [])
                                               (def `to (paramVars 0 params))
                                               (def `from (paramVars 0 params))

  defineRecord : NamedSafeDatatype → TC ⊤
  defineRecord (mk `dt params indices sop) = define (vArg `record) (type `dt) makeClauses
    where open WithParams params

defineDesc : (`desc : Name) → NamedSafeDatatype → TC ⊤
defineDesc `desc nsdt =
  let sdt = fst (removeNames nsdt) in
  do declareDef (vArg `desc) =<< quoteTC (SafeDatatypeToDesc sdt)
  ~| term ← quoteTC (safeDatatypeToDesc sdt)
  -| defineFun `desc [ clause [] term ]

defineRecord : Name → NamedSafeDatatype → TC ⊤
defineRecord `rec nsdt =
  do `desc ← freshName "desc"
  -| defineDesc `desc nsdt
  ~| `req ← freshName "req"
  -| Req.defineReq `req `desc nsdt
  ~| `to ← freshName "to"
  -| To.defineTo `to `desc `req nsdt
  ~| `from ← freshName "from"
  -| From.defineFrom `from `desc `req nsdt
  ~| Record.defineRecord `rec `desc `to `from nsdt
