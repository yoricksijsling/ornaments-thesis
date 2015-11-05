module ContextFree.One.Quoting.Safe where

open import Data.List using (List; []; _∷_; map; [_]; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function
open import Reflection
open import ContextFree.One.Desc
open import TypeArgs
open import Stuff using (foldrWithDefault; mapFoldrWithDefault)

data SafeArg : Set where
  SK : (S : Term) → SafeArg
  Svar : SafeArg

SafeProduct : Set
SafeProduct = (Name × List SafeArg)

SafeSum : Set
SafeSum = List SafeProduct

record SafeDatatype : Set where
  constructor mk
  field
    params : List (Sort × Arg Type)
    sop : SafeSum


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

  cclause₂ : Pattern → Pattern → Term → Clause
  cclause₂ p₁ p₂ t = clause (argvr p₁ ∷ argvr p₂ ∷ []) t

  cabsurd-clause₂ : Pattern → Pattern → Clause
  cabsurd-clause₂ p₁ p₂ = absurd-clause (argvr p₁ ∷ argvr p₂ ∷ [])

module ToDesc where
  ⟦_⟧arg : SafeArg → Term
  ⟦ SK S ⟧arg = ccon₁ (quote `K) S
  ⟦ Svar ⟧arg = ccon₀ (quote `var)

  ⟦_⟧product : SafeProduct → Term
  ⟦ n , as ⟧product = (foldrWithDefault (ccon₀ (quote `1))
                                        (ccon₂ (quote _`*_)) ∘′ map ⟦_⟧arg) as

  ⟦_⟧sum : SafeSum → Term
  ⟦_⟧sum = (foldrWithDefault (ccon₀ (quote `0))
                             (ccon₂ (quote _`+_))) ∘′ (map ⟦_⟧product)

  ⟦_⟧datatype : SafeDatatype → Term
  ⟦ mk params sop ⟧datatype = addArgsTm params ⟦ sop ⟧sum

module ToTo where
  VarTerm : Set
  VarTerm = (toᵢ : ℕ)(meᵢ : ℕ) → Term × ℕ

  ⟦_⟧arg-pat : SafeArg → Pattern
  ⟦ SK S ⟧arg-pat = var
  ⟦ Svar ⟧arg-pat = var

  -- De Bruijn index depends on the number of var patterns _after_ this arg
  ⟦_⟧arg-vt : SafeArg → VarTerm
  ⟦ SK S ⟧arg-vt toᵢ meᵢ = cvar₀ meᵢ , suc meᵢ
  ⟦ Svar ⟧arg-vt toᵢ meᵢ = cvar₁ toᵢ (cvar₀ meᵢ) , suc meᵢ

  ⟦_⟧product-pat : SafeProduct → Pattern
  ⟦ n , as ⟧product-pat = con n (map (argvr ∘′ ⟦_⟧arg-pat) as)

  ⟦_⟧product-term : SafeProduct → Term
  ⟦ n , as ⟧product-term = proj₁ (foldrWithDefault t1 t* (map ⟦_⟧arg-vt as) (length as) 0)
    where
    t1 : VarTerm
    t1 toᵢ meᵢ = ccon₀ (quote tt) , meᵢ
    t* : VarTerm → VarTerm → VarTerm
    t* x xs toᵢ meᵢ = let xs_tm , xs_meᵢ = xs toᵢ meᵢ in
                      let x_tm , x_meᵢ = x toᵢ xs_meᵢ in
                      ccon₂ (quote _,_) x_tm xs_tm , x_meᵢ

  ⟦_⟧sum : SafeSum → List Clause
  ⟦ ps ⟧sum = map (λ { (p , w) → cclause₂ var ⟦ p ⟧product-pat (w ⟦ p ⟧product-term) })
                  (zipWithWrappers ps id)
    where
    zipWithWrappers : {A : Set} → List A → (Term → Term) → List (A × (Term → Term))
    zipWithWrappers [] w = []
    zipWithWrappers (x ∷ []) w = [ x , ccon₁ (quote ⟨_⟩) ∘′ ccon₁ (quote inj₁) ]
    zipWithWrappers (x ∷ xs) w = let nw = w ∘′ ccon₁ (quote inj₂) in
                                 (x , nw) ∷ (zipWithWrappers xs nw)

  ⟦_⟧datatype : SafeDatatype → Term
  ⟦ mk params sop ⟧datatype = pat-lam ⟦ sop ⟧sum []
