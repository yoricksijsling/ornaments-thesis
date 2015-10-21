module Experiment1 where

open import Data.Empty
open import Data.Fin
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Vec
open import Function
open import Reflection
open import Relation.Binary.PropositionalEquality

data N : Set where
  ze : N
  su : N → N

data L (A : Set) : Set where
  [] : L A
  _∷_ : A → L A → L A

isDataType : Definition → Set
isDataType (function x) = ⊥
isDataType (data-type x) = ⊤
isDataType (record′ x) = ⊥
isDataType constructor′ = ⊥
isDataType axiom = ⊥
isDataType primitive′ = ⊥

module QuoteDataType where
  quoteDataType : (n : Name) → ⦃ p : isDataType (definition n) ⦄ → Data-type
  quoteDataType n {{p}} with definition n
  quoteDataType n {{()}} | function x
  quoteDataType n {{tt}} | data-type x = x
  quoteDataType n {{()}} | record′ x
  quoteDataType n {{()}} | constructor′
  quoteDataType n {{()}} | axiom
  quoteDataType n {{()}} | primitive′
  
  listLookup : ∀ {a} {A : Set a} → (xs : List A) → Fin (length xs) → A
  listLookup xs i = lookup i (fromList xs)
    where open import Data.Vec
  
  quoteConstructor : (dt : Data-type) → (i : Fin (length (constructors dt))) → Type
  quoteConstructor dt i = type (listLookup (constructors dt) i)
  
  `N : Data-type
  `N = quoteDataType (quote N)
  
  `N-nil : Type
  `N-nil = quoteConstructor `N (# 0)
  
  `N-cons : Type
  `N-cons = quoteConstructor `N (# 1)

module WithDT where

  record DT : Set where
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
  
  `N : DT
  `N = quoteDT (quote N)

  open import Signature

  blob : {!type (quote L.[])!}
  blob = {!quoteDT (quote L)!}

  -- blab : {!!}
  -- blab = {!definition (quote isDataType)!}



-- module MessingAbout where

--   data N : ⊤ → Set where
--     ze : N tt
--     su : N tt → N tt

--   -- data NL (A : Set) : Set where
--   --   zL : orn (quote )
--   --   sL : *pi A ()

--   data L (A : Set) : Set where
--     [] : L A
--     _∷_ : A → L A → L A

--   `N : Name
--   `N = quote N

--   -- NF-index : Type → Set {!!}
--   -- NF-index (el s t) = {!unquote t!}
--   -- NF-index : ∀ {l} → Set l → Set l
--   -- NF-index s = ℕ → s

--   NF-I : Set
--   NF-I = ℕ

--   NF-u : ⊤ → ℕ
--   NF-u

--   data NF : ℕ → Set where
--     -- NF-ze : ? 
--     -- NF-su : ?

--   data F : ℕ → Set where
--     ze : {n : ℕ} → F (suc n)
--     su : {n : ℕ} (i : F n) → F (suc n)

--   data V (A : Set) : ℕ → Set where
--     [] : V A zero
--     _∷_ : ∀ {n} (x : A) (xs : V A n) → V A (suc n)

--   -- data V` : (A : Set) → ℕ → Set₁ where
--   --   [] : ∀ A → V` A zero
--   --   _∷_ : ∀ A {n} (x : A) (xs : V` A n) → V` A (suc n)

