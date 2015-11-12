module ContextFree.One.Quoting where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; toℕ; #_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_; s≤s)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Product using (_×_; _,_; uncurry′; ∃; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map; length; drop)
open import Data.List.All using (all)
open import Data.Vec using (Vec; []; _∷_)
open import Data.String
open import Data.Unit using (⊤; tt)
open import Function
open import Reflection
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True)

open import ContextFree.One.Desc
open import ContextFree.One.Quoting.Constructor
open import ContextFree.One.Quoted
open import Data.Error
open Data.Error.Monad
open import TypeArgs
open import Stuff

getDatatype : Name → Error Data-type
getDatatype n with definition n
getDatatype n | data-type x = ok x
getDatatype n | otherwise = fail (showName n ++ " is not a data type")

_fits_ : ℕ → Name → Set
_fits_ p n = p ≤ paramCount (type n)

_fits?_ : ∀ p n → Dec (p fits n)
p fits? n = p ≤? paramCount (type n)

dtParams : (`dt : Name)(pc : ℕ) → Error (Vec Param pc)
dtParams `dt pc = proj₁ ∘′ takeParams (type `dt) pc
                <$> decToError "Too many params for datatype" (pc ≤? paramCount (type `dt))

quoteConstructors : (`dt : Name)(pc : ℕ)(dt : Data-type) → Error (List NamedSafeProduct)
quoteConstructors `dt pc dt =
  decToError "Too many params for some constructors"
             (all (λ `c → pc ≤? paramCount (type `c)) (constructors dt)) >>=
  sequenceM ∘′ mapAllToList (λ {`c} pc≤ → quoteConstructor `dt `c pc pc≤)

quoteDatatype : (`dt : Name)(pc : ℕ) → Error NamedSafeDatatype
quoteDatatype `dt pc =
  getDatatype `dt >>= λ dt →
  dtParams `dt pc >>= λ params →
  -- TODO: use params to check that constructors match exactly
  mk `dt pc params <$> quoteConstructors `dt pc dt

RunError : ∀{α}{A : Set α} → Error A → Set α
RunError {A = A} e = {isOk : True (isOk? e)} → A

quoteDatatype! : (n : Name) (p : ℕ) → RunError (quoteDatatype n p)
quoteDatatype! n p {isOk} = fromOk isOk



-- PARAMETERS / INDICES

-- data ListP (A : Set) : Set where
--   nilP : ListP A
--   consP : A → ListP A → ListP A

-- data ListI : (A : Set) → Set₁ where
--   nilI : ∀{A} → ListI A
--   consI : ∀{A} → A → ListI A → ListI A

-- type (quote Dummy)  ≡ el₁ (sort (lit 0))
-- type (quote ListP)  ≡ el₁ (pi (argvr (el₁ (sort (lit 0))))
--                               (el₁ (sort (lit 0))))
-- type (quote ListI)  ≡ el₂ (pi (argvr (el₁ (sort (lit 0))))
--                               (el₂ (sort (lit 1))))
-- type (quote nilP)   ≡ el₁ (pi (arghr (el₁ (sort (lit 0))))
--                               (el₀ (def (quote ListP) (argvr (var 0 []) ∷ []))))
-- type (quote nilI)   ≡ el₁ (pi (arghr (el₁ (sort (lit 0))))
--                               (el₁ (def (quote ListI) (argvr (var 0 []) ∷ []))))
