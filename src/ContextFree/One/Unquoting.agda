module ContextFree.One.Unquoting where

open import Common
open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.Params
open import ContextFree.One.Quoted
open import Reflection
open import Stuff using (zipNats; zipNatsDown)

private
  paramArgs : ∀{tp}(offset : Nat){pc : Nat} → Vec Param pc → List (Arg ⟦ tp ⟧tp)
  paramArgs {tp} offset = zipNatsDown offset tm ∘ vecToList
    where tm : Nat → Param → Arg ⟦ tp ⟧tp
          tm offset (param₀ v s) = arg (arg-info v relevant) (`var₀ offset s)

  paramPats : {pc : Nat} → Vec Param pc → List (Arg Pattern)
  paramPats = paramArgs 0 -- If it is used as a pattern, the offset is ignored

  module _ where
    test-paramArgs-t : paramArgs {tp-term} 1 (param₀ visible "a" ∷ param₀ visible "b" ∷ [])
                     ≡ vArg (var 2 []) ∷ vArg (var 1 []) ∷ []
    test-paramArgs-t = refl

    test-paramArgs-p : paramArgs {tp-patt} 1 (param₀ visible "a" ∷ param₀ visible "b" ∷ [])
                     ≡ vArg (var "a") ∷ vArg (var "b") ∷ []
    test-paramArgs-p = refl

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
  termArgs : Name → List (SafeArg {pc}) → List Term
  termArgs `f as = zipNatsDown 0 termArg as
    where
    termArg : Nat → SafeArg {pc} → Term
    termArg meᵢ (Spar i) = `var₀ meᵢ ""
    termArg meᵢ Srec = def `f (paramArgs (length as) params ++ [ vArg (`var₀ meᵢ "") ])

module To (`to `desc : Name) where
  module WithParams {pc : Nat}(params : Vec Param pc) where
    open AlphaBeta
    open ToFrom params

    makeClause : Nat → NamedSafeProduct {pc} → Clause
    makeClause i (`con , as) = clause (paramPats params ++ [ vArg (α `con $ patArgs as) ])
                                      (β i $ termArgs `to as)

    makeClauses : NamedSafeSum → List Clause
    makeClauses = zipNats makeClause

    type : (`dt : Name) → Type
    type `dt = addParams (vecToList params) $
               def `dt (paramArgs 0 params)
                 `→ `def₁ (quote μ) (def `desc (paramArgs 1 params))

  defineTo : NamedSafeDatatype → TC ⊤
  defineTo (mk `dt pc params sop) = define (vArg `to) (type `dt) (makeClauses sop)
    where open WithParams params

module From (`from `desc : Name) where
  module WithParams {pc : Nat}(params : Vec Param pc) where
    open AlphaBeta
    open ToFrom params

    α-term : NamedSafeProduct {pc} → Term
    α-term (`con , as) = α `con (termArgs `from as)

    β-pattern : Nat → NamedSafeProduct {pc} → Pattern
    β-pattern i (`con , as) = β i (patArgs as)

    β-last : Nat → Pattern
    β-last n = `con₁ (quote ⟨_⟩) ((right^ n) absurd)

    makeClause : Nat → NamedSafeProduct {pc} → Clause
    makeClause i (`con , as) = clause (paramPats params ++ [ vArg (β i $ patArgs as) ])
                                      (α `con $ termArgs `from as)

    makeClauses : NamedSafeSum → List Clause
    makeClauses ps = zipNats makeClause ps
                   ++ [ absurd-clause (paramPats params ++ [ vArg (β-last (length ps)) ]) ]

    type : (`dt : Name) → Type
    type `dt = addParams (vecToList params) $
               `def₁ (quote μ) (def `desc (paramArgs 0 params))
                 `→ def `dt (paramArgs 1 params)

  defineFrom : NamedSafeDatatype → TC ⊤
  defineFrom (mk `dt pc params sop) = define (vArg `from) (type `dt) (makeClauses sop)
    where open WithParams params

module Record (`record `desc `to `from : Name) where
  module WithParams {pc : Nat}(params : Vec Param pc) where
    type : (`dt : Name) → Type
    type `dt = addParams (vecToList params) $
               `def₁ (quote RawIsContextFree) (def `dt (paramArgs 0 params))

    makeClauses : List Clause
    makeClauses = [_] $ clause (paramPats params) $
                  `con₃ (quote RawIsContextFree.mk) (def `desc (paramArgs 0 params))
                                                    (def `to (paramArgs 0 params))
                                                    (def `from (paramArgs 0 params))

  defineRecord : NamedSafeDatatype → TC ⊤
  defineRecord (mk `dt pc params sop) = define (vArg `record) (type `dt) makeClauses
    where open WithParams params

defineDesc : (`desc : Name) → NamedSafeDatatype → TC ⊤
defineDesc `desc nsdt =
  let sdt = fst (unnameSafeDatatype nsdt) in
  do declareDef (vArg `desc) =<< quoteTC (DescFun sdt)
  ~| term ← quoteTC (descFun sdt)
  -| defineFun `desc [ clause [] term ]

defineRecord : Name → NamedSafeDatatype → TC ⊤
defineRecord `rec nsdt =
  do `desc ← freshName "desc"
  -| `to ← freshName "to"
  -| `from ← freshName "from"
  -| defineDesc `desc nsdt
  ~| To.defineTo `to `desc nsdt
  ~| From.defineFrom `from `desc nsdt
  ~| Record.defineRecord `rec `desc `to `from nsdt
