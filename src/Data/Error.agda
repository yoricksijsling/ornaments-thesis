module Data.Error where

open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Data.Product
open import Data.String using (String)
open import Data.Unit
open import Function
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)

module MessagesModule where
  infixr 5 _∷_

  data Messages : Set₁ where
    [] : Messages
    _∷_ : {S : Set}(s : S) → Messages → Messages

  [_] : {S : Set}(s : S) → Messages
  [ s ] = s ∷ []

  infixr 5 _++_

  _++_ : Messages → Messages → Messages
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ xs ++ ys

open MessagesModule using (Messages; []; _∷_) public
open MessagesModule

Error : ∀{α}(A : Set α) → Set (lsuc lzero ⊔ α)
Error A = Messages × Maybe A

ok : ∀{α}{A : Set α}(x : A) → Error A
ok x = [] , just x

fail : ∀{α}{A : Set α}{S : Set}(s : S) → Error A
fail s = [ s ] , nothing

fromMaybe : ∀{α}{A : Set α} → String → Maybe A → Error A
fromMaybe s (just x) = ok x
fromMaybe s nothing = fail s

IsOk : ∀{α}{A : Set α} → Error A → Set α
IsOk = Is-just ∘′ proj₂

isOk? : ∀{α}{A : Set α}(e : Error A) → Dec (IsOk e)
isOk? (ms , just x) = yes (just tt)
isOk? (ms , nothing) = no λ { () }

fromOk : ∀{α}{A : Set α}{e : Error A}(isOk : True (isOk? e)) → A
fromOk {e = ms , just x} tt = x
fromOk {e = ms , nothing} ()

decToError : ∀{α}{A : Set α}{S : Set}(s : S) → Dec A → Error A
decToError s (yes p) = ok p
decToError s (no ¬p) = fail s

log : {S : Set}(s : S) → Error ⊤
log s = [ s ] , just tt

module Monad where
  -- We can't use a monad record because we want to use it at different levels.
  return : ∀{α}{A : Set α} → A → Error A
  return = ok

  infixl 1 _>>=_ _>>_

  _>>=_ : ∀{α β}{A : Set α}{B : Set β} → Error A → (A → Error B) → Error B
  ms , just x >>= f = let fms , b = f x in ms ++ fms , b
  ms , nothing >>= f = ms , nothing

  _>>_ : ∀{α β}{A : Set α}{B : Set β} → Error A → Error B → Error B
  a >> b = a >>= (const b)


  infixl 4 _<$>_ _<*>_

  _<$>_ : ∀{α β}{A : Set α}{B : Set β} → (f : A → B) → Error A → Error B
  f <$> a = a >>= return ∘′ f

  _<*>_ : ∀{α β}{A : Set α}{B : Set β} → (f : Error (A → B)) → Error A → Error B
  f <*> a = f >>= λ f′ →
            a >>= λ a′ →
            return (f′ a′)

  sequenceM : ∀{α}{A : Set α} → List (Error A) → Error (List A)
  sequenceM [] = ok []
  sequenceM (a ∷ as) = _∷_ <$> a <*> sequenceM as

  mapM : ∀{α β}{A : Set α}{B : Set β} → (A → Error B) → List A → Error (List B)
  mapM f [] = ok []
  mapM f (a ∷ as) = _∷_ <$> f a <*> mapM f as
