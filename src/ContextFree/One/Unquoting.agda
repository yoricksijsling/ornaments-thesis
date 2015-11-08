open import Reflection

module ContextFree.One.Unquoting (`Desc : Name)(`μ : Name) where

open import Data.List using (List; []; _∷_; map; [_]; _++_; _∷ʳ_; length; foldr)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Stream using (Stream; iterate)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function
open import Reflection

open import ContextFree.One.Desc
open import ContextFree.One.Quoted
open import TypeArgs
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

  cvar₀ : ℕ → Term
  cvar₀ n = var n []
  cvar₁ : ℕ → Term → Term
  cvar₁ n t = var n (argvr t ∷ [])

  cdef₀ : Name → Term
  cdef₀ n = def n []
  cdef₁ : Name → Term → Term
  cdef₁ n t = def n (argvr t ∷ [])

  cclause₀ : Term → Clause
  cclause₀ t = clause [] t
  cclause₁ : Pattern → Term → Clause
  cclause₁ p₁ t = clause (argvr p₁ ∷ []) t
  cclause₂ : Pattern → Pattern → Term → Clause
  cclause₂ p₁ p₂ t = clause (argvr p₁ ∷ argvr p₂ ∷ []) t

  cabsurd-clause₂ : Pattern → Pattern → Clause
  cabsurd-clause₂ p₁ p₂ = absurd-clause (argvr p₁ ∷ argvr p₂ ∷ [])

  paramArgs : ℕ → List (Sort × Arg Type) → List (Arg Term)
  paramArgs n = zipStreamBackwards (λ { n (_ , arg i _) → arg i (cvar₀ n) })
                                   (iterate suc n)

  paramPats : List (Sort × Arg Type) → List (Arg Pattern)
  paramPats params = map (λ { (_ , arg i _) → arg i var }) params

  wrappers : ∀{tp} → Stream (tpv tp → tpv tp)
  wrappers = Data.Stream.map (λ w → ccon₁ (quote ⟨_⟩) ∘′ w ∘′ ccon₁ (quote inj₁))
           $ iterate (_∘′_ (ccon₁ (quote inj₂))) id

  lastPattern : ℕ → Pattern
  lastPattern = ccon₁ (quote ⟨_⟩) ∘′ helper
    where helper : ℕ → Pattern
          helper zero = absurd
          helper (suc n) = ccon₁ (quote inj₂) (helper n)

module MakeDesc where
  ⟦_⟧arg : SafeArg → Term
  ⟦ SK S ⟧arg = ccon₁ (quote `K) S
  ⟦ Svar ⟧arg = ccon₀ (quote `var)

  ⟦_⟧product : SafeProduct → Term
  ⟦_⟧product = foldr (λ a as → ccon₂ (quote _`*_) ⟦ a ⟧arg as)
                     (ccon₀ (quote `1)) ∘′ proj₂

  ⟦_⟧sum : SafeSum → Term
  ⟦_⟧sum = foldr (λ p ps → ccon₂ (quote _`+_) ⟦ p ⟧product ps)
                 (ccon₀ (quote `0))

  ⟦_⟧datatype : SafeDatatype → FunctionDef
  ⟦ mk dtname params sop ⟧datatype = fun-def (addArgs params (el (lit 1) (def `Desc [])))
                                             [ cclause₀ (addArgsTm params ⟦ sop ⟧sum) ]

module MakeTo (`desc : Name)(`to : Name) where

  module WithParams (params : List (Sort × Arg Type)) where
    ⟦_⟧arg-pat : SafeArg → Pattern
    ⟦ SK S ⟧arg-pat = var
    ⟦ Svar ⟧arg-pat = var

    module WithProductLength (total : ℕ) where
      -- meᵢ is the De Bruijn index of the pattern variable corresponding to this arg
      ⟦_⟧arg-term : SafeArg → (meᵢ : ℕ) → Term
      ⟦ SK S ⟧arg-term meᵢ = cvar₀ meᵢ
      ⟦ Svar ⟧arg-term meᵢ = def `to (paramArgs total params ∷ʳ argvr (cvar₀ meᵢ))

    ⟦_⟧product-pat : SafeProduct → Pattern
    ⟦ `con , as ⟧product-pat = con `con (map (argvr ∘′ ⟦_⟧arg-pat) as)

    ⟦_⟧product-term : SafeProduct → Term
    ⟦ `con , as ⟧product-term = foldr (ccon₂ (quote _,_)) (ccon₀ (quote tt))
                              $ zipStreamBackwards (flip ⟦_⟧arg-term) (iterate suc 0) as
      where open WithProductLength (length as)

    ⟦_⟧sum : SafeSum → List Clause
    ⟦_⟧sum = zipStream makeclause wrappers
      where makeclause = λ wrap p → clause (paramPats params ∷ʳ argvr ⟦ p ⟧product-pat)
                                           (wrap ⟦ p ⟧product-term)

  ⟦_⟧datatype : SafeDatatype → FunctionDef
  ⟦ mk dtname params sop ⟧datatype = fun-def (addArgs params base) ⟦ sop ⟧sum
    where
    open WithParams params
    base : Type
    base = el (lit 0) (pi (argvr (el (lit 0) (def dtname (paramArgs 0 params))))
                          (el (lit 0) (cdef₁ `μ (def `desc (paramArgs 1 params)))))

module MakeFrom (`desc : Name)(`from : Name) where
  module WithParams (params : List (Sort × Arg Type)) where
    ⟦_⟧arg-pat : SafeArg → Pattern
    ⟦ SK S ⟧arg-pat = var
    ⟦ Svar ⟧arg-pat = var

    module WithProduct (`con : Name)(total : ℕ) where
      ⟦_⟧arg-term : SafeArg → (meᵢ : ℕ) → Term
      ⟦ SK S ⟧arg-term meᵢ = cvar₀ meᵢ
      ⟦ Svar ⟧arg-term meᵢ = def `from (paramArgs total params ∷ʳ argvr (cvar₀ meᵢ))

    ⟦_⟧product-pat : SafeProduct → Pattern
    ⟦ `con , as ⟧product-pat = foldr (ccon₂ (quote _,_)) (ccon₀ (quote tt))
                             $ map ⟦_⟧arg-pat as

    ⟦_⟧product-term : SafeProduct → Term
    ⟦ `con , as ⟧product-term = con `con
                              $ map argvr
                              $ zipStreamBackwards (flip ⟦_⟧arg-term) (iterate suc 0) as
      where
      open WithProduct `con (length as)

    ⟦_⟧sum : SafeSum → List Clause
    ⟦ ps ⟧sum = zipStream makeclause wrappers ps
              ∷ʳ absurd-clause (paramPats params ∷ʳ argvr (lastPattern (length ps)))
      where makeclause = λ wrap p → clause (paramPats params ∷ʳ argvr (wrap (⟦ p ⟧product-pat)))
                                           ⟦ p ⟧product-term

  ⟦_⟧datatype : SafeDatatype → FunctionDef
  ⟦ mk dtname params sop ⟧datatype = fun-def (addArgs params base) ⟦ sop ⟧sum
    where
    open WithParams params
    base : Type
    base = el (lit 0) (pi (argvr (el (lit 0) (cdef₁ `μ (def `desc (paramArgs 0 params)))))
                          (el (lit 0) (def dtname (paramArgs 1 params))))

makeDesc : SafeDatatype → FunctionDef
makeDesc = MakeDesc.⟦_⟧datatype

makeTo : Name → Name → SafeDatatype → FunctionDef
makeTo = MakeTo.⟦_⟧datatype

makeFrom : Name → Name → SafeDatatype → FunctionDef
makeFrom = MakeFrom.⟦_⟧datatype
