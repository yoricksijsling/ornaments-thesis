module Experiment2 where

open import Data.Empty
open import Data.Fin
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Vec
open import Function
open import Reflection
open import Relation.Binary.PropositionalEquality

-- Parameters and indices are the same in reflection!

-- data N : ⊤ → Set where
--   ze : N tt
--   su : N tt → N tt

-- data L (A : Set) : ⊤ → Set where
--   [] : L A tt
--   _∷_ : A → L A tt → L A tt

data N : Set where
  ze : N
  su : N → N

data L (A : Set) : Set where
  [] : L A
  _∷_ : A → L A → L A

data F : ℕ → Set where
  ze : {n : ℕ} → F (suc n)
  su : {n : ℕ} (i : F n) → F (suc n)

data V (A : Set) : ℕ → Set where
  [] : V A zero
  _∷_ : ∀ {n} (x : A) (xs : V A n) → V A (suc n)

-- Witness that a definition is a data-type
isDataType : Definition → Set
isDataType (function x) = ⊥
isDataType (data-type x) = ⊤
isDataType (record′ x) = ⊥
isDataType constructor′ = ⊥
isDataType axiom = ⊥
isDataType primitive′ = ⊥

-- Convert multiple pi's to a list of arguments
uncurry` : Type → List (Arg Type) × Type
uncurry` (el s (var x args)) = [] , el s (var x args)
uncurry` (el s (con c args)) = [] , el s (con c args)
uncurry` (el s (def f args)) = [] , el s (def f args)
uncurry` (el s (lam v t)) = [] , el s (lam v t)
uncurry` (el s (pat-lam cs args)) = [] , el s (pat-lam cs args)
uncurry` (el s (pi a t)) with uncurry` t
uncurry` (el s (pi a _)) | as , r = a ∷ as , r
uncurry` (el s (sort x)) = [] , el s (sort x)
uncurry` (el s (lit x)) = [] , el s (lit x)
uncurry` (el s unknown) = [] , el s unknown

curry` : List (Arg Type) → Type → Type
curry` [] r = r
curry` (a ∷ as) r = el unknown (pi a (curry` as r))

module CurryUncurry where
  -- Does not hold because we insert `unknown` sorts in curry`
  -- curry-uncurry-id : ∀ t → (uncurry curry`) (uncurry` t) ≡ t
  -- curry-uncurry-id (el s t) = {!!}

  -- Only works if we assume that r is not a pi
  -- uncurry-curry-id : ∀ as r → uncurry` (curry` as r) ≡ (as , r)
  -- uncurry-curry-id [] (el s (var x args)) = refl
  -- uncurry-curry-id [] (el s (con c args)) = refl
  -- uncurry-curry-id [] (el s (def f args)) = refl
  -- uncurry-curry-id [] (el s (lam v t)) = refl
  -- uncurry-curry-id [] (el s (pat-lam cs args)) = refl
  -- uncurry-curry-id [] (el s (pi t₁ t₂)) = {!!} -- Only works 
  -- uncurry-curry-id [] (el s (sort x)) = refl
  -- uncurry-curry-id [] (el s (lit x)) = refl
  -- uncurry-curry-id [] (el s unknown) = refl
  -- uncurry-curry-id (a ∷ as) r with uncurry-curry-id as r
  -- uncurry-curry-id (a ∷ as) r | eq with uncurry` (curry` as r)
  -- uncurry-curry-id (a ∷ as) r | refl | .(as , r) = refl

------------------------------------------------------------

record DT : Set where
  constructor mk
  field
    nm : Name
    ty : Type
    {n} : ℕ
    cs : Vec (Name × Type) n

quoteDT : (n : Name) → ⦃ p : isDataType (definition n) ⦄ → DT
quoteDT n {{p}} with definition n
quoteDT n {{()}} | function x
quoteDT n {{tt}} | data-type dt = record
  { nm = n
  ; ty = type n
  ; cs = Data.Vec.map < id , type > (fromList (constructors dt)) }
quoteDT n {{()}} | record′ x
quoteDT n {{()}} | constructor′
quoteDT n {{()}} | axiom
quoteDT n {{()}} | primitive′

countArgs : DT → ℕ
countArgs = length ∘ proj₁ ∘ uncurry` ∘ DT.ty

`N : DT
`N = quoteDT (quote N)
-- `N = {!quoteDT (quote N)!}
-- mk (quote N) (el (lit 1) (sort (lit 0)))
-- ((quote N.ze , el (lit 0) (def (quote N) [])) ∷
--  (quote N.su ,
--   el (lit 0)
--   (pi
--    (arg (arg-info visible relevant) (el (lit 0) (def (quote N) [])))
--    (el (lit 0) (def (quote N) []))))
--  ∷ [])

--------------------------------------------------------------------------------

record DT2 : Set where
  constructor mk
  field
    nm : Name
    -- {ps#} : ℕ
    parameters : List (Arg Type)
    indices : List (Arg Type)
    ty : Type
    {cs#} : ℕ
    cs : Vec (Name × Type) cs#

-- open import Signature

-- toSig : (dt : DT ) → Sig (getIndex dt)
-- toSig = {!!}
