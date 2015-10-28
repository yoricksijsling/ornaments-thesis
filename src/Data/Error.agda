module Data.Error where

open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Data.String
open import Function
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True)

data Error {α}(A : Set α) : Set α where
  ok : (x : A) → Error A
  fail : (s : String) → Error A

error : ∀{α β}{A : Set α}{B : Error A → Set β} →
        ((x : A) → B (ok x)) → ((s : String) → B (fail s)) → (x : Error A) → B x
error o f (ok x) = o x
error o f (fail s) = f s

fromMaybe : ∀{α}{A : Set α} → String → Maybe A → Error A
fromMaybe s (just x) = ok x
fromMaybe s nothing = fail s

data IsOk {α}{A : Set α} : Error A → Set α where
  ok : (a : A) → IsOk (ok a)

isOk? : ∀{α}{A : Set α}(e : Error A) → Dec (IsOk e)
isOk? (ok x) = yes (ok x)
isOk? (fail s) = no λ { () }

fromOk : ∀{α}{A : Set α}(e : Error A){isOk : True (isOk? e)} → A
fromOk (ok x) {tt} = x
fromOk (fail s) {()}

module Monad where
  -- We can't use a monad record because we want to use it at different levels.
  return : ∀{α}{A : Set α} → A → Error A
  return = ok

  infixl 1 _>>=_ _>>_

  _>>=_ : ∀{α β}{A : Set α}{B : Set β} → Error A → (A → Error B) → Error B
  ok a >>= f = f a
  fail s >>= f = fail s

  _>>_ : ∀{α β}{A : Set α}{B : Set β} → Error A → Error B → Error B
  a >> b = a >>= (const b)

  mapM : ∀{α β}{A : Set α}{B : Set β} → (A → Error B) → List A → Error (List B)
  mapM f [] = ok []
  mapM f (a ∷ as) = f a >>= λ b →
                    mapM f as >>= λ bs →
                    return (b ∷ bs)
