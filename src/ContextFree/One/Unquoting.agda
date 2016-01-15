open import Reflection

-- The quoted names of these types have to be passed from the calling module.
-- Even though we can quote them ourselves, Agda throws an internal exception
-- when we quote the name here and then unquote it in another file.
module ContextFree.One.Unquoting (`Desc : Name)(`μ : Name)(`RawIsContextFree : Name) where

open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.Params
open import ContextFree.One.Quoted
open import Data.Fin using (toℕ)
open import Data.List
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Stream using (Stream; iterate)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; toList)
open import Function
open import Reflection
open import Stuff using (zipStream; zipStreamBackwards)

private
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
  tpf {tp-term} ft fp = ft ∘′ map argvr
  tpf {tp-patt} ft fp = fp ∘′ map argvr

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

  cvar : ∀{tp} → ℕ → List (tpv tp) → tpv tp
  cvar n = tpf (var n) (const var)
  cvar₀ : ∀{tp} → ℕ → tpv tp
  cvar₀ n = cvar n []

  cdef₁ : Name → Term → Term
  cdef₁ n t = def n (argvr t ∷ [])

  paramArgs : ∀{tp}(offset : ℕ){pc : ℕ} → Vec Param pc → List (Arg (tpv tp))
  paramArgs {tp} offset = zipStreamBackwards tm (iterate suc offset) ∘′ toList
    where tm : ℕ → Param → Arg (tpv tp)
          tm offset (param₀ v) = arg (arg-info v relevant) (cvar₀ offset)

  paramPats : {pc : ℕ} → Vec Param pc → List (Arg Pattern)
  paramPats = paramArgs 0 -- If it is used as a pattern, the offset is not used

  inj₂^_ : ∀{tp} → ℕ → tpv tp → tpv tp
  inj₂^_ zero = id
  inj₂^_ (suc n) = ccon₁ (quote inj₂) ∘′ (inj₂^ n)

module MakeAlphaBeta {pc : ℕ}{tp : TP}(recArgWrapper : tpv tp → tpv tp) where
  αβ-arg : (meᵢ : ℕ) → SafeArg {pc} → tpv tp
  αβ-arg meᵢ (Spar i) = cvar₀ meᵢ
  αβ-arg meᵢ Srec = recArgWrapper (cvar₀ meᵢ)

  -- constructorᵢ x₁ ⋯ xn
  α : NamedSafeProduct {pc} → tpv tp
  α (`con , as) = ccon `con (zipStreamBackwards αβ-arg (iterate suc 0) as)

  -- ⟨ inj₂ⁱ (inj₁ (x₁ , ⋯ , xn , tt)) ⟩
  β : (i : ℕ) → NamedSafeProduct {pc} → tpv tp
  β i (`con , as) = ccon₁ (quote ⟨_⟩) ∘′ (inj₂^ i) ∘′ ccon₁ (quote inj₁)
                  $ foldr (ccon₂ (quote _,_)) (ccon₀ (quote tt))
                  $ zipStreamBackwards αβ-arg (iterate suc 0) as

module MakeTo (`to : Name)(`desc : Name) where

  module WithParams (pc : ℕ)(params : Vec Param pc) where
    open MakeAlphaBeta

    β-term : ℕ → NamedSafeProduct {pc} → Term
    β-term i (`con , as) = β (λ x → def `to (paramArgs (length as) params ∷ʳ argvr x))
                             i (`con , as)

    makeClause : ℕ → NamedSafeProduct {pc} → Clause
    makeClause i p = clause (paramPats params ∷ʳ argvr (α id p))
                            (β-term i p)

    makeClauses : NamedSafeSum → List Clause
    makeClauses = zipStream makeClause (iterate suc 0)

  makeFunction : NamedSafeDatatype → FunctionDef
  makeFunction (mk `dt pc params sop) = fun-def (addParams (toList params) base) (makeClauses sop)
    where
    open WithParams pc params
    base : Type
    base = el (lit 0) (pi (argvr (el (lit 0) (def `dt (paramArgs 0 params))))
                          (el (lit 0) (cdef₁ `μ (def `desc (paramArgs 1 params)))))

module MakeFrom (`from : Name)(`desc : Name) where
  module WithParams (pc : ℕ)(params : Vec Param pc) where
    open MakeAlphaBeta

    α-term : NamedSafeProduct {pc} → Term
    α-term (`con , as) = α (λ x → def `from (paramArgs (length as) params ∷ʳ argvr x))
                           (`con , as)

    β-last : ℕ → Pattern
    β-last n = ccon₁ (quote ⟨_⟩) ((inj₂^ n) absurd)

    makeClause : ℕ → NamedSafeProduct {pc} → Clause
    makeClause i p = clause (paramPats params ∷ʳ argvr (β id i p))
                            (α-term p)

    makeClauses : NamedSafeSum → List Clause
    makeClauses ps = zipStream makeClause (iterate suc 0) ps
                   ∷ʳ absurd-clause (paramPats params ∷ʳ argvr (β-last (length ps)))

  makeFunction : NamedSafeDatatype → FunctionDef
  makeFunction (mk `dt pc params sop) = fun-def (addParams (toList params) base) (makeClauses sop)
    where
    open WithParams pc params
    base : Type
    base = el (lit 0) (pi (argvr (el (lit 0) (cdef₁ `μ (def `desc (paramArgs 0 params)))))
                          (el (lit 0) (def `dt (paramArgs 1 params))))

makeTo : (`to `desc : Name) → NamedSafeDatatype → FunctionDef
makeTo = MakeTo.makeFunction

makeFrom : (`from `desc : Name) → NamedSafeDatatype → FunctionDef
makeFrom = MakeFrom.makeFunction

makeRecord : (`desc `to `from : Name) → NamedSafeDatatype → FunctionDef
makeRecord `desc `to `from (mk `dt pc params sop) = fun-def (addParams (toList params) basetype)
                                                            [ clause (paramPats params) term ]
  where
  basetype : Type
  basetype = el (lit 1) (cdef₁ `RawIsContextFree (def `dt (paramArgs 0 params)))
  term : Term
  term = ccon₃ (quote RawIsContextFree.mk) (def `desc (paramArgs 0 params))
                                           (def `to (paramArgs 0 params))
                                           (def `from (paramArgs 0 params))
