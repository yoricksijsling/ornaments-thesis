module Experiment3 where

open import Data.Empty
open import Data.Fin
open import Data.List
-- open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Vec
open import Function
open import Reflection
open import Relation.Binary.PropositionalEquality

mutual
  data SPTest : Set

  SPTest' : ℕ → Set
  SPTest' zero = SPTest
  SPTest' (suc n) = ⊥

  SPTest→SPTest : ℕ → Set
  SPTest→SPTest zero = SPTest → SPTest
  SPTest→SPTest (suc n) = ⊥
  
  data SPTest where
    -- flop : (SPTest → SPTest) → SPTest -- not strictly positive
    -- flop : (n : ℕ) → (SPTest' n → id SPTest) → SPTest -- not strictly positive
    ok : id SPTest → SPTest -- ok
    -- flop : (n : ℕ) → SPTest→SPTest n → SPTest
    

-- module DataLib where
--   -- n is aantal parameters
--   data Desc (n : ℕ) : Set₁ where
--     `X : Desc n -- recursive
--     `P : (v : Fin n) → Desc n --`var
--     `K : Term → Desc n
--   --  `1 : Desc
--   --  _`×_ : (S T : Desc) → Desc
--   --  `Π ‵Σ : (S : Term)(T : Desc) → Desc
  
--   -- Binnenste List: [] ≈ `1 en _∷_ ≈ `×
--   -- Buitenste List: _∷_ ≈ `Σ
--   TDesc : ℕ → Set₁
--   TDesc n = List (List (Desc n))

--   ListD : TDesc 1
--   ListD = [] ∷ (`P zero ∷ `X ∷ []) ∷ []

--   -- Voordeel aan deze representatie is dat je geen geneste datatypes kan maken (sum of products of sums of products)

-- module TransportingFunctions where
--   -- infixr 30 _`×_
  
--   data IDesc (I : Set) : Set₁ where
--     `var : (i : I) → IDesc I
--     `1 : IDesc I
--     `Σ : (S : Set )(T : S → IDesc I) → IDesc I
--     `Π : (S : Set )(T : S → IDesc I) → IDesc I
--     -- Redundant (but first-order) connectives:
--     _`×_ : (A B : IDesc I) → IDesc I
--     `σ : (n : ℕ)(T : Fin n → IDesc I) → IDesc I
--     -- Vecs and functions with a finite domain are isomorphic:
--     -- `σ : (n : ℕ)(T : Vec (IDesc I) n) → IDesc I

--   -- IDesc's hebben wel indices maar geen parameters

--   record func (I J : Set) : Set₁ where
--     constructor mk
--     field out : J → IDesc I

--   ListD : Set → func ⊤ ⊤
--   ListD A = func.mk λ _ →
--          `σ 2 
--             (λ { zero → `1 
--                ; (suc zero) → `Σ A λ _ → `var tt
--                ; (suc (suc ())) })
  
--   --   `X : Desc n -- recursive
--   --   `P : (v : Fin n) → Desc n --`var
--   --   `K : Term → Desc n
--   -- --  `1 : Desc
--   -- --  _`×_ : (S T : Desc) → Desc
--   -- --  `Π ‵Σ : (S : Term)(T : Desc) → Desc

-- -- Products in datatype, sums daarbuiten om de structuur af te dwingen. Sums van IDesc gebruiken tags of ℕ's, moeten wij dat doen? Gewoon een List lijkt voldoende.

-- NTup : Set → ℕ → Set
-- NTup A zero = ⊤
-- NTup A (suc zero) = A
-- NTup A (suc (suc n)) = A × NTup A (suc n)

-- -- data CDesc (n : ℕ) : Set where
-- --   `X : CDesc n
-- --   `P : (v : Fin n) → CDesc n
-- --   `K : Term → CDesc n

-- -- data PDesc (n : ℕ) : Set where
-- --   `π : (k : ℕ) → (NTup (CDesc n) k) → PDesc n

-- -- data Desc (n : ℕ) : Set where
-- --   `σ : (k : ℕ) → (NTup (PDesc n) k) → Desc n

-- data CDesc (n : ℕ) : Set where
--   `X : CDesc n
--   `P : (v : Fin n) → CDesc n
--   `K : Term → CDesc n
--   -- `Σ : Arg Type
--   -- `Π : 

-- data PDesc (n : ℕ) : Set where
--   `π : (k : ℕ) → (NTup (CDesc n) k) → PDesc n

-- data Desc (n : ℕ) : Set where
--   `σ : (k : ℕ) → (NTup (PDesc n) k) → Desc n

-- -- ((quote N.ze , el (lit 0) (def (quote N) [])) ∷
-- --  (quote N.su ,
-- --   el (lit 0)
-- --   (pi
-- --    (arg (arg-info visible relevant) (el (lit 0) (def (quote N) [])))
-- --    (el (lit 0) (def (quote N) []))))
-- --  ∷ [])

-- DNat : Desc 0
-- DNat = `σ 2 ({!!} , {!!}) --(`π 0 tt , `π 1 `X)

-- -- DList : Desc 1
-- -- DList = `σ 2 (`π 0 tt , `π 2 {!!})
