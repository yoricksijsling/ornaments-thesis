open import Builtin.Reflection

module ContextFree.One.Unquoting where

open import Common
open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.Params
open import ContextFree.One.Quoted
open import Stuff using (zipNats; zipNatsDown)

private
  FunctionDef : Set
  FunctionDef = Type × List Clause

  fun-def : Type → List Clause → FunctionDef
  fun-def = _,_

  argvr : ∀{A} → A → Arg A
  argvr = arg (arg-info visible relevant)

  data TP : Set where
    tp-term : TP
    tp-patt : TP

  tpv : TP → Set
  tpv tp-term = Term
  tpv tp-patt = Pattern

  tpf : ∀{tp} → (List (Arg Term) → Term) →
               (List (Arg Pattern) → Pattern) →
               List (tpv tp) → tpv tp
  tpf {tp-term} ft fp = ft ∘ map argvr
  tpf {tp-patt} ft fp = fp ∘ map argvr

  ccon : ∀{tp} → Name → List (tpv tp) → tpv tp
  ccon n = tpf (con n) (con n)
  ccon₀ : ∀{tp} → Name → tpv tp
  ccon₀ n = ccon n []
  ccon₁ : ∀{tp} → Name → tpv tp → tpv tp
  ccon₁ n t₁ = ccon n (t₁ ∷ [])
  ccon₂ : ∀{tp} → Name → tpv tp → tpv tp → tpv tp
  ccon₂ n t₁ t₂ = ccon n (t₁ ∷ t₂ ∷ [])
  ccon₃ : ∀{tp} → Name → tpv tp → tpv tp → tpv tp → tpv tp
  ccon₃ n t₁ t₂ t₃ = ccon n (t₁ ∷ t₂ ∷ t₃ ∷ [])

  cvar : ∀{tp} → Nat → String → List (tpv tp) → tpv tp
  cvar n s = tpf (var n) (const (var s))
  cvar₀ : ∀{tp} → Nat → String → tpv tp
  cvar₀ n s = cvar n s []

  cdef₁ : Name → Term → Term
  cdef₁ n t = def n (argvr t ∷ [])

  paramArgs : ∀{tp}(offset : Nat){pc : Nat} → Vec Param pc → List (Arg (tpv tp))
  paramArgs {tp} offset = zipNatsDown offset tm ∘ vecToList
    where tm : Nat → Param → Arg (tpv tp)
          tm offset (param₀ v s) = arg (arg-info v relevant) (cvar₀ offset s)

  paramPats : {pc : Nat} → Vec Param pc → List (Arg Pattern)
  paramPats = paramArgs 0 -- If it is used as a pattern, the offset is ignored

  module _ where
    test-paramArgs-t : paramArgs {tp-term} 1 (param₀ visible "a" ∷ param₀ visible "b" ∷ [])
                     ≡ argvr (var 2 []) ∷ argvr (var 1 []) ∷ []
    test-paramArgs-t = refl

    test-paramArgs-p : paramArgs {tp-patt} 1 (param₀ visible "a" ∷ param₀ visible "b" ∷ [])
                     ≡ argvr (var "a") ∷ argvr (var "b") ∷ []
    test-paramArgs-p = refl

  right^_ : ∀{tp} → Nat → tpv tp → tpv tp
  right^_ zero = id
  right^_ (suc n) = ccon₁ (quote right) ∘ (right^ n)

module AlphaBeta where
  -- constructorᵢ x₁ ⋯ xn
  α : ∀{tp} → Name → List (tpv tp) → tpv tp
  α `con = ccon `con

  -- ⟨ inj₂ⁱ (inj₁ (x₁ , ⋯ , xn , tt)) ⟩
  β : ∀{tp} → (i : Nat) → List (tpv tp) → tpv tp
  β i = ccon₁ (quote ⟨_⟩) ∘ right^ i ∘ ccon₁ (quote left)
       ∘ foldr (ccon₂ (quote _,_)) (ccon₀ (quote ⊤.tt))

module ToFrom {pc : Nat}(params : Vec Param pc) where
  -- Given a list of arguments [a, x, y, b, z], where xyz are recursive arguments
  -- Returns a list of patterns [a, x, y, b, z]
  patArgs : List (SafeArg {pc}) → List Pattern
  patArgs as = zipNatsDown 0 (λ meᵢ a → cvar₀ meᵢ "") as

  -- Given a list of arguments [a, x, y, b, z], where xyz are recursive arguments
  -- Returns a list of terms [a, `f x, `f y, b, `f z]
  termArgs : Name → List (SafeArg {pc}) → List Term
  termArgs `f as = zipNatsDown 0 termArg as
    where
    termArg : Nat → SafeArg {pc} → Term
    termArg meᵢ (Spar i) = cvar₀ meᵢ ""
    termArg meᵢ Srec = def `f (paramArgs (length as) params ++ [ argvr (cvar₀ meᵢ "") ])

module To (`to `desc : Name) where
  module WithParams {pc : Nat}(params : Vec Param pc) where
    open AlphaBeta
    open ToFrom params

    makeClause : Nat → NamedSafeProduct {pc} → Clause
    makeClause i (`con , as) = clause (paramPats params ++ [ argvr (α `con $ patArgs as) ])
                                      (β i $ termArgs `to as)

    makeClauses : NamedSafeSum → List Clause
    makeClauses = zipNats makeClause

  make : NamedSafeDatatype → FunctionDef
  make (mk `dt pc params sop) = fun-def (addParams (vecToList params) base) (makeClauses sop)
    where
    open WithParams params
    base : Type
    base = pi (argvr (def `dt (paramArgs 0 params)))
              (abs ("_") (cdef₁ (quote μ) (def `desc (paramArgs 1 params))))

module From (`from `desc : Name) where
  module WithParams {pc : Nat}(params : Vec Param pc) where
    open AlphaBeta
    open ToFrom params

    α-term : NamedSafeProduct {pc} → Term
    α-term (`con , as) = α `con (termArgs `from as)

    β-pattern : Nat → NamedSafeProduct {pc} → Pattern
    β-pattern i (`con , as) = β i (patArgs as)

    β-last : Nat → Pattern
    β-last n = ccon₁ (quote ⟨_⟩) ((right^ n) absurd)

    makeClause : Nat → NamedSafeProduct {pc} → Clause
    makeClause i (`con , as) = clause (paramPats params ++ [ argvr (β i $ patArgs as) ])
                                      (α `con $ termArgs `from as)

    makeClauses : NamedSafeSum → List Clause
    makeClauses ps = zipNats makeClause ps
                   ++ [ absurd-clause (paramPats params ++ [ argvr (β-last (length ps)) ]) ]

  make : NamedSafeDatatype → FunctionDef
  make (mk `dt pc params sop) = fun-def (addParams (vecToList params) base) (makeClauses sop)
    where
    open WithParams params
    base : Type
    base = pi (argvr (cdef₁ (quote μ) (def `desc (paramArgs 0 params))))
              (abs "_" (def `dt (paramArgs 1 params)))

module Record (`desc `to `from : Name) where
  make : NamedSafeDatatype → FunctionDef
  make (mk `dt pc params sop) = fun-def (addParams (vecToList params) basetype)
                                               [ clause (paramPats params) term ]
    where
    basetype : Type
    basetype = cdef₁ (quote RawIsContextFree) (def `dt (paramArgs 0 params))
    term : Term
    term = ccon₃ (quote RawIsContextFree.mk) (def `desc (paramArgs 0 params))
                                             (def `to (paramArgs 0 params))
                                             (def `from (paramArgs 0 params))

module Define where
  defineDesc : (`desc : Name) → NamedSafeDatatype → TC ⊤
  defineDesc `desc nsdt =
    let sdt = fst (unnameSafeDatatype nsdt) in
    do declareDef (argvr `desc) =<< quoteTC (DescFun sdt)
    ~| term ← quoteTC (descFun sdt)
    -| defineFun `desc [ clause [] term ]

  defineFunctionDef : Name → FunctionDef → TC ⊤
  defineFunctionDef n fd = uncurry (define (argvr n)) fd

defineRec : Name → NamedSafeDatatype → TC ⊤
defineRec `rec nsdt =
  do `desc ← freshName "desc"
  -| `to ← freshName "to"
  -| `from ← freshName "from"
  -| defineDesc `desc nsdt
  ~| defineFunctionDef `to (To.make `to `desc nsdt)
  ~| defineFunctionDef `from (From.make `from `desc nsdt)
  ~| defineFunctionDef `rec (Record.make `desc `to `from nsdt)
  where open Define
