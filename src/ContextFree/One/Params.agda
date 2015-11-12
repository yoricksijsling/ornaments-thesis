module ContextFree.One.Params where

open import Data.List
open import Data.Nat.Base
open import Data.Product using (_×_; _,_; uncurry′) renaming (map to map×)
open import Data.Vec using (Vec; []; _∷_)
open import Function
open import Reflection
open import Relation.Binary.PropositionalEquality

pattern arg-pat s a t = el s (pi (arg (arg-info visible relevant) a) t)

data ArgView : Type → Set where
  arg : (s : Sort)(a : Type)(t : Type) → ArgView (arg-pat s a t)
  rest : (t : Type) → ArgView t

argView : (t : Type) → ArgView t
argView (arg-pat s a t) = arg s a t
argView t = rest t

getArgs : (t : Type) → List (Sort × Type) × Type
getArgs t with argView t
getArgs ._ | arg s a t = map× (_∷_ (s , a)) id (getArgs t)
getArgs ._ | rest t = [] , t


data Param : Set where
  param₀ : (v : Visibility) → Param

pattern param₀-pat v t = el (lit 1) (pi (arg (arg-info v relevant) (el (lit 1) (sort (lit 0)))) t)

data ParamView : Type → Set where
  param₀ : (v : Visibility)(t : Type) → ParamView (param₀-pat v t)
  rest : (t : Type) → ParamView t

paramView : (t : Type) → ParamView t
paramView (param₀-pat v t) = param₀ v t
paramView t = rest t

paramCount : Type → ℕ
paramCount t with paramView t
paramCount ._ | param₀ v t = suc (paramCount t)
paramCount t | rest .t = 0

takeParams : (t : Type)(n : ℕ)(p : n ≤ paramCount t) → Vec Param n × Type
takeParams t zero p = [] , t
takeParams t (suc n) p with paramView t
takeParams ._ (suc n) (s≤s p) | param₀ v t = map× (_∷_ (param₀ v)) id (takeParams t n p)
takeParams ._ (suc n) () | rest t

addParams : List Param → Type → Type
addParams [] target = target
addParams (param₀ v ∷ args) target = param₀-pat v (addParams args target)

addParamsTm : List Param → Term → Term
addParamsTm [] target = target
addParamsTm (param₀ v ∷ ps) target = lam v (addParamsTm ps target)

module _ where
  addTakeParams : ∀ t n p → uncurry′ (addParams ∘′ Data.Vec.toList) (takeParams t n p) ≡ t
  addTakeParams t zero p = refl
  addTakeParams t (suc n) p with paramView t
  addTakeParams ._ (suc n) (s≤s p) | param₀ v t = cong (param₀-pat v) (addTakeParams t n p)
  addTakeParams ._ (suc n) () | rest t
