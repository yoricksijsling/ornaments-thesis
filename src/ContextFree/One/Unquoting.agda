open import Reflection

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

  ccon₀ : ∀{tp} → Name → tpv tp
  ccon₀ n = tpf (con n) (con n) []
  ccon₁ : ∀{tp} → Name → tpv tp → tpv tp
  ccon₁ n t₁ = tpf (con n) (con n) (t₁ ∷ [])
  ccon₂ : ∀{tp} → Name → tpv tp → tpv tp → tpv tp
  ccon₂ n t₁ t₂ = tpf (con n) (con n) (t₁ ∷ t₂ ∷ [])
  ccon₃ : ∀{tp} → Name → tpv tp → tpv tp → tpv tp → tpv tp
  ccon₃ n t₁ t₂ t₃ = tpf (con n) (con n) (t₁ ∷ t₂ ∷ t₃ ∷ [])

  cvar₀ : ℕ → Term
  cvar₀ n = var n []
  cvar₁ : ℕ → Term → Term
  cvar₁ n t = var n (argvr t ∷ [])

  cdef₀ : Name → Term
  cdef₀ n = def n []
  cdef₁ : Name → Term → Term
  cdef₁ n t = def n (argvr t ∷ [])

  cabsurd-clause₂ : Pattern → Pattern → Clause
  cabsurd-clause₂ p₁ p₂ = absurd-clause (argvr p₁ ∷ argvr p₂ ∷ [])

  paramArgs : (offset : ℕ){pc : ℕ} → Vec Param pc → List (Arg Term)
  paramArgs offset = zipStreamBackwards tm (iterate suc offset) ∘′ toList
    where tm : ℕ → Param → Arg Term
          tm offset (param₀ v) = arg (arg-info v relevant) (cvar₀ offset)

  paramPats : {pc : ℕ} → Vec Param pc → List (Arg Pattern)
  paramPats = map pt ∘′ toList
    where pt : Param → Arg Pattern
          pt (param₀ v) = arg (arg-info v relevant) var

  wrappers : ∀{tp} → Stream (tpv tp → tpv tp)
  wrappers = Data.Stream.map (λ w → ccon₁ (quote ⟨_⟩) ∘′ w ∘′ ccon₁ (quote inj₁))
           $ iterate (_∘′_ (ccon₁ (quote inj₂))) id

  lastPattern : ℕ → Pattern
  lastPattern = ccon₁ (quote ⟨_⟩) ∘′ helper
    where helper : ℕ → Pattern
          helper zero = absurd
          helper (suc n) = ccon₁ (quote inj₂) (helper n)


module MakeTo (`to : Name)(`desc : Name) where

  module WithParams (pc : ℕ)(params : Vec Param pc) where
    ⟦_⟧arg-pat : SafeArg {pc} → Pattern
    ⟦ Spar i ⟧arg-pat = var
    ⟦ Srec ⟧arg-pat = var

    module WithProductLength (total : ℕ) where
      -- meᵢ is the De Bruijn index of the pattern variable corresponding to this arg
      ⟦_⟧arg-term : SafeArg {pc} → (meᵢ : ℕ) → Term
      ⟦ Spar i ⟧arg-term meᵢ = cvar₀ meᵢ
      ⟦ Srec ⟧arg-term meᵢ = def `to (paramArgs total params ∷ʳ argvr (cvar₀ meᵢ))

    ⟦_⟧product-pat : NamedSafeProduct → Pattern
    ⟦ `con , as ⟧product-pat = con `con (map (argvr ∘′ ⟦_⟧arg-pat) as)

    ⟦_⟧product-term : NamedSafeProduct → Term
    ⟦ `con , as ⟧product-term = foldr (ccon₂ (quote _,_)) (ccon₀ (quote tt))
                              $ zipStreamBackwards (flip ⟦_⟧arg-term) (iterate suc 0) as
      where open WithProductLength (length as)

    ⟦_⟧sum : NamedSafeSum → List Clause
    ⟦_⟧sum = zipStream makeclause wrappers
      where makeclause = λ wrap p → clause (paramPats params ∷ʳ argvr ⟦ p ⟧product-pat)
                                           (wrap ⟦ p ⟧product-term)

  ⟦_⟧datatype : NamedSafeDatatype → FunctionDef
  ⟦ mk `dt pc params sop ⟧datatype = fun-def (addParams (toList params) base) ⟦ sop ⟧sum
    where
    open WithParams pc params
    base : Type
    base = el (lit 0) (pi (argvr (el (lit 0) (def `dt (paramArgs 0 params))))
                          (el (lit 0) (cdef₁ `μ (def `desc (paramArgs 1 params)))))

module MakeFrom (`from : Name)(`desc : Name) where
  module WithParams (pc : ℕ)(params : Vec Param pc) where
    ⟦_⟧arg-pat : SafeArg {pc} → Pattern
    ⟦ Spar i ⟧arg-pat = var
    ⟦ Srec ⟧arg-pat = var

    module WithProduct (`con : Name)(total : ℕ) where
      ⟦_⟧arg-term : SafeArg {pc} → (meᵢ : ℕ) → Term
      ⟦ Spar i ⟧arg-term meᵢ = cvar₀ meᵢ
      ⟦ Srec ⟧arg-term meᵢ = def `from (paramArgs total params ∷ʳ argvr (cvar₀ meᵢ))

    ⟦_⟧product-pat : NamedSafeProduct → Pattern
    ⟦ `con , as ⟧product-pat = foldr (ccon₂ (quote _,_)) (ccon₀ (quote tt))
                             $ map ⟦_⟧arg-pat as

    ⟦_⟧product-term : NamedSafeProduct → Term
    ⟦ `con , as ⟧product-term = con `con
                              $ map argvr
                              $ zipStreamBackwards (flip ⟦_⟧arg-term) (iterate suc 0) as
      where
      open WithProduct `con (length as)

    ⟦_⟧sum : NamedSafeSum → List Clause
    ⟦ ps ⟧sum = zipStream makeclause wrappers ps
              ∷ʳ absurd-clause (paramPats params ∷ʳ argvr (lastPattern (length ps)))
      where makeclause = λ wrap p → clause (paramPats params ∷ʳ argvr (wrap (⟦ p ⟧product-pat)))
                                           ⟦ p ⟧product-term

  ⟦_⟧datatype : NamedSafeDatatype → FunctionDef
  ⟦ mk `dt pc params sop ⟧datatype = fun-def (addParams (toList params) base) ⟦ sop ⟧sum
    where
    open WithParams pc params
    base : Type
    base = el (lit 0) (pi (argvr (el (lit 0) (cdef₁ `μ (def `desc (paramArgs 0 params)))))
                          (el (lit 0) (def `dt (paramArgs 1 params))))

makeTo : (`to : Name) → (`desc : Name) → NamedSafeDatatype → FunctionDef
makeTo = MakeTo.⟦_⟧datatype

makeFrom : (`from : Name) → (`desc : Name) → NamedSafeDatatype → FunctionDef
makeFrom = MakeFrom.⟦_⟧datatype

makeRecord : (`desc : Name) → (`to : Name) → (`from : Name) → NamedSafeDatatype → FunctionDef
makeRecord `desc `to `from (mk `dt pc params sop) = fun-def (addParams (toList params) basetype)
                                                            [ clause (paramPats params) term ]
  where
  basetype : Type
  basetype = el (lit 1) (cdef₁ `RawIsContextFree (def `dt (paramArgs 0 params)))
  term : Term
  term = ccon₃ (quote RawIsContextFree.mk) (def `desc (paramArgs 0 params))
                                           (def `to (paramArgs 0 params))
                                           (def `from (paramArgs 0 params))
