{-# OPTIONS --type-in-type #-}

module DataQuote where

open import Reflection

open import Function

open import Category.Monad

open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Relation.Unary hiding (∅)


open import Data.Nat
open import Data.Fin hiding (_+_ ; _≤_)
open import Data.Vec hiding (_>>=_ ; [_] ; foldr)
open import Data.List
open import Data.List.Any renaming (Any to AnyL)
open import Data.List.All renaming (All to AllL)
open import Data.Unit hiding (_≤?_ ; _≤_)
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Maybe

open import Relation.Binary.PropositionalEquality hiding ([_])

-- * Library: quoted type and term constructors

-- TODO: Move to stdlib

`⊤` : Term
`⊤` = def (quote ⊤) []

`⊥` : Term
`⊥` = def (quote ⊥) []

_`×`_ : Term → Term → Term
S `×` T = def (quote _×_) 
              (arg (arg-info visible relevant) S
              ∷ arg (arg-info visible relevant) T 
              ∷ [])

_`⊎`_ : Term → Term → Term
S `⊎` T = def (quote _⊎_) 
              (arg (arg-info visible relevant) S
              ∷ arg (arg-info visible relevant) T 
              ∷ [])

lamᵛ : Term → Term
lamᵛ = lam visible

argᵛʳ : ∀{A} → A → Arg A
argᵛʳ = arg (arg-info visible relevant)

-- * Library: traversal

-- TODO: Are traversable functors defined somewhere?

traverseL : ∀{a : Set}{b : Set} → (a → Maybe b) → List a → Maybe (List b)
traverseL f [] = just []
traverseL f (x ∷ xs) = 
  f x >>= λ x → 
  traverseL f xs >>= λ xs → 
  return (x ∷ xs)
  where open RawMonad {_} Data.Maybe.monad

-- * Universe of descriptions

-- ** Code

-- TODO: Extend to dependent sorts
-- TODO: Extend to inductive families
-- TODO: Record names of arguments

data Desc (n : ℕ) : Set₁ where
  `X : Desc n
  `P : (v : Fin n) → Desc n
  `K : Term → Desc n
--  `1 : Desc
--  _`×_ : (S T : Desc) → Desc
--  `Π ‵Σ : (S : Term)(T : Desc) → Desc

-- TODO: Record names of constructors

TDesc : ℕ → Set₁
TDesc n = List (List (Desc n))

-- *** Examples

module Test where

  NatD : TDesc 0
  NatD = [] ∷ (`X ∷ []) ∷ []
  
  ListD : TDesc 1
  ListD = [] ∷ (`P zero ∷ `X ∷ []) ∷ []

  TreeD : TDesc 2
  TreeD = [ `P zero ] ∷ (`P (suc zero) ∷ `X ∷ `X ∷ []) ∷ []

-- ** Interpretation

`Any` : ∀{A} → (A → Term) → List A → Term
`Any` f xs = foldr (λ a tm → f a `⊎` tm) `⊥` xs

-- TODO: Switch `pi` instead of uncurrified form:

`All` : ∀{A} → (A → Term) → List A → Term
`All` f xs = foldr (λ a tm → f a `×` tm) `⊤` xs

⟦_⟧D : ∀ {n} → Desc n → Name → Vec Term n → Term
⟦ `X ⟧D X Ps = def X (toList (Data.Vec.map argᵛʳ Ps))
⟦ `P i ⟧D X Ps = Data.Vec.lookup i Ps
⟦ `K S ⟧D X Ps = S

⟦_⟧ : ∀{n} → TDesc n → Name → Vec Term n → Term
⟦ xs ⟧ X Ps = `Any` (`All` (λ D → ⟦ D ⟧D X Ps)) xs 


-- TODO: Support other sorts than 'Set₀'
sortD : ∀ {n} → TDesc n → Term
sortD _ = sort (lit 0)


-- TODO: what kind of term goes on the left of the semi in a 'data' def?
--paramD : ∀{n} → TDesc n → Term
--paramD _ = {!!} 
  -- where tel : ℕ → Term
  --       tel 0 = sort (lit 0)
  --       tel (suc n) = pi (argᵛʳ (el (lit 0) (var n []))) (el (lit 0) (tel n))

vlookup : ∀{A} → (n : ℕ)(xs : List A)(q : suc n ≤ length xs) → A
vlookup m xs q 
  with length xs | inspect length xs 
vlookup m xs () 
  | zero | q'
vlookup m [] q
  | suc n | Reveal_is_.[ () ]
vlookup zero (x ∷ xs) q 
  | suc n | q' = x
vlookup (suc m) (x ∷ xs) (s≤s q)
  | suc .(length xs) | Reveal_is_.[ refl ] = vlookup m xs q

_as_∋_ : ∀{n} → (T : TDesc n)(D : Name)(k : ℕ){q : True (suc k ≤? (length T))} → Term
_as_∋_ {params} T D k {q} with suc k ≤? length T
... | yes p =
  let Ps : Vec Term params
      Ps = Data.Vec.tabulate {params} (λ k → var ((params ℕ-ℕ (raise 1 k))) []) in
  let Ps' : Vec Term params
      Ps' = Data.Vec.tabulate {params} (λ k → var (suc (params ℕ-ℕ (raise 1 k))) []) in
  pi (arg (arg-info visible relevant)
     -- HACK: this is (needlessly) binding variable '0'
     -- forcing Ps' to be computed from 1
          (el (lit 0) 
              (`All` (λ T → ⟦ T ⟧D D Ps)  
                     (vlookup k T p))))
     (el (lit 0) (def D (toList (Data.Vec.map argᵛʳ Ps'))))
(T as D ∋ k) {()} | no ¬p

-- *** Examples:

module Test-Nat where
  open Test

  data ℕ' : Set where
    con : unquote (⟦ NatD ⟧ (quote ℕ') []) → ℕ'

  ze : ℕ'
  ze = con (inj₁ tt)

  su : ℕ' → ℕ'
  su n = con (inj₂ (inj₁ (n , tt)))

  data ℕ'' : unquote (sortD NatD) where 
    ze'' : unquote (NatD as (quote ℕ'') ∋ zero)
    su'' : unquote (NatD as (quote ℕ'') ∋ suc zero)

  test-ze'' : ℕ''
  test-ze'' = ze'' tt

  test-su'' : ℕ'' → ℕ''
  test-su'' n = su'' (n , tt)


module Test-List where
  open Test

  -- TODO: Is there a nicer way than de Bruijn to capture the 'A'?  
  data List' (A : Set) : Set where
    con : unquote (⟦ ListD ⟧ (quote List') ((var 0 []) ∷ [])) → List' A

  nil' : ∀{A} → List' A
  nil' = con (inj₁ tt)

  cons' : ∀{A} → A → List' A → List' A
  cons' a xs = con (inj₂ (inj₁ (a , xs , tt)))

  data List'' (A : Set) : unquote (sortD ListD) where
    nil'' : unquote (ListD as (quote List'') ∋ zero)
    cons'' : unquote (ListD as (quote List'') ∋ suc zero)

  test-nil'' : ∀{A} → List'' A
  test-nil'' = nil'' tt

  test-cons'' : ∀{A} → A → List'' A → List'' A
  test-cons'' a xs = cons'' (a , xs , tt)

module Test-Tree where
  open Test

  data Tree' (A B : Set) : Set where
    con : unquote (⟦ TreeD ⟧ (quote Tree') ((var 1 []) ∷ (var 0 []) ∷ [])) → Tree' A B

  leaf' : ∀{A B} → A → Tree' A B
  leaf' a = con (inj₁ (a , tt))

  node' : ∀{A B} → B → Tree' A B → Tree' A B → Tree' A B
  node' b l r = con (inj₂ (inj₁ (b , l , r , tt) ))

  data Tree'' (A B : Set) : unquote (sortD TreeD) where
    leaf'' : unquote (TreeD as (quote Tree'') ∋ zero)
    node'' : unquote (TreeD as (quote Tree'') ∋ suc zero)

  test-leaf'' : ∀{A B} → A → Tree'' A B 
  test-leaf'' a = leaf'' (a , tt)

  test-node'' : ∀{A B} → B → Tree'' A B → Tree'' A B → Tree'' A B
  test-node'' b l r = node'' (b , l , r , tt)

-- * Structured quoting of inductives:

-- ** Elaboration monad

-- The [ElabM] computation gives us access to the name of the
-- datatype under elaboration and lets us signal a failure.

ElabM : Set → Set
ElabM X = Name → Maybe X

getName : ElabM Name
getName n = just n

elabMon : RawMonad ElabM
elabMon = Data.Maybe.monadT (record { return = λ a → λ _ → a 
                                    ; _>>=_ = λ ma mf s → mf (ma s) s })
elabMonZero : RawMonadZero ElabM
elabMonZero = record { monad = elabMon
                     ; ∅ = λ _ → nothing }

-- TODO: Instanciate ElabM as a traversable functor

traverseE : ∀{a : Set}{b : Set} → (a → ElabM b) → List a → ElabM (List b)
traverseE elab xs name = traverseL (λ a → elab a name) xs

open RawMonadZero ⦃ ... ⦄

-- ** Example: Structure of an inductive definition (List)

module Test-StructureList where

  listN : Name
  listN = quote List

  listT : Type
  listT = type listN
  {-
    el unknown
      (pi
        (arg (arg-info hidden relevant)
             (el (lit 0) (def Agda.Primitive.Level [])))
        (el unknown
          (pi
            (arg (arg-info visible relevant)
                 (el unknown (sort (set (var 0 [])))))
            (el unknown (sort unknown)))))
  -}

  listD : Data-type
  listD with definition listN | inspect definition listN
  listD | data-type D | t = D
  listD | function x | Reveal_is_.[ () ]
  listD | record′ x | Reveal_is_.[ () ]
  listD | constructor′ | Reveal_is_.[ () ]
  listD | axiom | Reveal_is_.[ () ]
  listD | primitive′ | Reveal_is_.[ () ]

  cstorsList : List Name
  cstorsList = constructors listD

  nilN : Name
  nilN with cstorsList | inspect Data.List.length cstorsList
  nilN | [] | Reveal_is_.[ () ]
  nilN | x ∷ [] | Reveal_is_.[ () ]
  nilN | nil ∷ cons ∷ [] | Reveal_is_.[ _ ] = nil
  nilN | x ∷ x₁ ∷ x₂ ∷ t | Reveal_is_.[ () ]

  consN : Name
  consN with cstorsList | inspect Data.List.length cstorsList
  consN | [] | Reveal_is_.[ () ]
  consN | x ∷ [] | Reveal_is_.[ () ]
  consN | nil ∷ cons ∷ [] | Reveal_is_.[ _ ] = nil
  consN | x ∷ x₁ ∷ x₂ ∷ t | Reveal_is_.[ () ]

  nilT : Type
  nilT = type nilN
  {-
    el unknown
      (pi
        (arg (arg-info hidden relevant)
             (el (lit 0) (def Agda.Primitive.Level [])))
        (el unknown
            (pi
              (arg (arg-info hidden relevant)
                   (el unknown (sort (set (var 0 [])))))
              (el unknown
                (def Data.List.List
                     (arg (arg-info hidden relevant) (var 1 []) ∷
                      arg (arg-info visible relevant) (var 0 []) ∷ []))))))
  -}

  consT : Type
  consT = type consN
  {-
    el unknown
      (pi
        (arg (arg-info hidden relevant)
             (el (lit 0) (def Agda.Primitive.Level [])))
        (el unknown
          (pi
            (arg (arg-info hidden relevant)
                 (el unknown (sort (set (var 0 [])))))
            (el unknown
              (def Data.List.List
                (arg (arg-info hidden relevant) (var 1 []) ∷
                arg (arg-info visible relevant) (var 0 []) ∷ []))))))
  -}


-- ** Elaboration

-- Intuitively, the elaboration process is simply a parser whose token
-- are 'Term's and whose outputs are 'TDesc's. This parser is
-- described in the 'ElabM' monad and ran over the 'Name' of a
-- (supposedly inductive) definition. It may fail if:
--   1. It is not an inductive definition
--   2. The parser is not able to cope with it (someday, that will be
--      considered a bug)

run : ElabM (Σ ℕ TDesc) → Name → Maybe (Σ ℕ TDesc)
run elab n = elab n

-- The parser is structured by the format of inductive definitions:

--   1. |quoteData| quotes a top-level 'data' definition, making sure
--      that the provided name is indeed an inductive definition:

quoteData : ElabM (Σ ℕ TDesc)

--   2. |quoteConstructors| quotes its sum of constructors:

quoteConstructors : ∀{n} → Definition → ElabM (TDesc n)

--   3. |quoteArg| quotes the product of arguments of a single constructor

quoteConstructor : ∀{n} → Type → ElabM (List (Desc n))

--   4. |quoteD| quotes individual arguments, distinguishing recursive
--      arguments, parameters, and constant sets.

quoteArg : ∀{n} → Type → ElabM (Desc n)

-- Now for the codes:

mutual
  parseParamsT : Term → ElabM ℕ
  parseParamsT (pi (arg (arg-info hidden relevant) _) t) 
    = -- Level argument
      -- TODO: This test is incorrect, just dropping irrelevant args 
      parseParams t
  parseParamsT (pi (arg _ s) t) 
    = -- Parameter
      parseParams t >>= λ n → 
      return (1 + n)
  parseParamsT (sort x) 
    = -- End of telescope 
      return 0
  parseParamsT _ = ∅

  parseParams : Type → ElabM ℕ
  parseParams (el _ t) = parseParamsT t


quoteData = 
  getName >>= λ name → 
  parseParams (type name) >>= λ params →
  quoteConstructors {n = params} (definition name) >>= λ cstors →
  return (params , cstors)
    


{-
  (λ rec →
    maybeData constructors (definition rec)) >>= λ cstors →
  (λ rec → traverseL (λ name → quoteArg (type name) rec) cstors) >>= λ args →
  return args
  where maybeData : ∀{A : Set} → (Data-type → A) → Definition → Maybe A
        maybeData f (data-type x) = return (f x)
        maybeData f _ = ∅
-}

quoteConstructors (data-type D) = 
  traverseE (λ cstor-name → quoteConstructor (type cstor-name)) 
            (constructors D) 
quoteConstructors _ = ∅

quoteConstructor (el s t) = quoteConstructorT t 
  where quoteConstructorT : ∀{n} → Term → ElabM (List (Desc n))
        quoteConstructorT (pi (arg (arg-info visible _) t₁) t₂) = 
        -- Actual, explicit argument:
           quoteArg t₁ >>= λ t₁ → 
           quoteConstructor t₂ >>= λ t₂ → 
           return (t₁ ∷ t₂)
        quoteConstructorT (pi (arg (arg-info _ _) _) t) = 
          -- Implicit or parameter type:
          -- TODO: support implicit arguments
          quoteConstructor t 
        quoteConstructorT (def name args) =
          -- End of telescope
          return []
        quoteConstructorT _  _ = 
          -- Unsupported: everything else
          ∅


quoteArg (el _ t) = quoteArgTerm t
  where quoteArgTerm : ∀{n} → Term → ElabM (Desc n)
        quoteArgTerm (def f args) rec with rec ≟-Name f 
        quoteArgTerm (def f args) rec | yes p 
          = -- Recursive argument:
            return `X
        quoteArgTerm (def f args) rec | no ¬p 
          = -- Constant set:
            return (`K (def f args))
        quoteArgTerm {n} (var v []) rec with (suc v) ≤? n 
        quoteArgTerm (var v []) rec | yes p
          = -- Parameter:
            return (`P (fromℕ≤ p))
        quoteArgTerm (var v []) rec | no ¬p = ∅
        quoteArgTerm (var x args) rec = ∅
        quoteArgTerm (pi t₁ t₂) rec = ∅
        quoteArgTerm (con c args) rec = ∅
        quoteArgTerm (lam v tm) rec = ∅
        quoteArgTerm (sort x) rec = ∅
        quoteArgTerm unknown rec = ∅

-- *** Examples:

module NatD where

  NatD' : Maybe (Σ ℕ TDesc)
  NatD' = quoteData (quote ℕ)

  test : NatD' ≡ just (0 , [] ∷ (`X ∷ []) ∷ [])
  test = refl

module ListD where

  ListD' : Maybe (Σ ℕ TDesc)
  ListD' = quoteData (quote List) 

  test : ListD' ≡ just (1 , [] ∷ (`P zero ∷ `X ∷ []) ∷ [])
  test = refl

module TreeD where

  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    node : B → Tree A B → Tree A B → Tree A B

  TreeD' : Maybe (Σ ℕ TDesc)
  TreeD' = quoteData (quote Tree)

  test : TreeD' ≡ just (2 , (`P (suc zero) ∷ []) ∷ (`P zero ∷ `X ∷ `X ∷ []) ∷ [])
  test = refl
