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

  ccon₀ : Name → Term
  ccon₀ n = con n []
  ccon₁ : Name → Term → Term
  ccon₁ n t = con n (argvr t ∷ [])
  ccon₂ : Name → Term → Term → Term
  ccon₂ n t₁ t₂ = con n (argvr t₁ ∷ argvr t₂ ∷ [])

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

  VarTerm : Set
  VarTerm = (total : ℕ)(meᵢ : ℕ) → Term × ℕ

  module WithParams (params : List (Sort × Arg Type)) where
    paramArgs : ℕ → List (Arg Term)
    paramArgs n = zipStreamBackwards (λ { (_ , arg i _) n → arg i (var n []) })
                                            params (iterate suc n)

    paramPats : List (Arg Pattern)
    paramPats = map (λ { (_ , arg i _) → arg i var }) params

    ⟦_⟧arg-pat : SafeArg → Pattern
    ⟦ SK S ⟧arg-pat = var
    ⟦ Svar ⟧arg-pat = var

    -- De Bruijn index depends on the number of var patterns _after_ this arg
    ⟦_⟧arg-vt : SafeArg → VarTerm
    ⟦ SK S ⟧arg-vt total meᵢ = cvar₀ meᵢ , suc meᵢ
    ⟦ Svar ⟧arg-vt total meᵢ = def `to (paramArgs total ∷ʳ argvr (cvar₀ meᵢ)) , suc meᵢ

    ⟦_⟧product-pat : SafeProduct → Pattern
    ⟦ n , as ⟧product-pat = con n (map (argvr ∘′ ⟦_⟧arg-pat) as)

    ⟦_⟧product-term : SafeProduct → Term
    ⟦ n , as ⟧product-term = proj₁ (foldr t* (ccon₀ (quote tt) , 0) as)
      where t* : SafeArg → Term × ℕ → Term × ℕ
            t* a (t , meᵢ) = let a_tm , a_meᵢ = ⟦ a ⟧arg-vt (length as) meᵢ in
                             (ccon₂ (quote _,_) a_tm t) , a_meᵢ

    ⟦_⟧sum : SafeSum → List Clause
    ⟦ ps ⟧sum = zipStream (λ p wrap → clause (paramPats ∷ʳ argvr ⟦ p ⟧product-pat)
                                             (wrap ⟦ p ⟧product-term))
                          ps wrappers
      where wrappers : Stream (Term → Term)
            wrappers = Data.Stream.map (λ w → ccon₁ (quote ⟨_⟩) ∘′ w ∘′ ccon₁ (quote inj₁))
                                       (iterate (_∘′_ (ccon₁ (quote inj₂))) id)

  ⟦_⟧datatype : SafeDatatype → FunctionDef
  ⟦ mk dtname params sop ⟧datatype = fun-def (addArgs params base) ⟦ sop ⟧sum
    where
    open WithParams params
    base : Type
    base = el (lit 0) (pi (argvr (el (lit 0) (def dtname (paramArgs 0))))
                          (el (lit 0) (cdef₁ `μ (def `desc (paramArgs 1)))))

makeDesc : SafeDatatype → FunctionDef
makeDesc = MakeDesc.⟦_⟧datatype

makeTo : Name → Name → SafeDatatype → FunctionDef
makeTo = MakeTo.⟦_⟧datatype
