module TypeArgs where

open import Data.Fin
open import Data.Fin.Properties
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Vec
open import Function
open import Reflection
open import Relation.Binary.PropositionalEquality

argCount : Type → ℕ
argCount (el s (pi t₁ t₂)) = suc (argCount t₂)
argCount otherwise = zero

addArgs : List (Sort × Arg Type) → Type → Type
addArgs [] target = target
addArgs ((s , argt) ∷ args) target = el s (pi argt (addArgs args target))

takeArgs : (t : Type) → (k : Fin (suc (argCount t))) → Vec (Sort × Arg Type) (toℕ k) × Type
takeArgs t zero = [] , t
takeArgs (el s (pi argt t₂)) (suc k) = let args , target = takeArgs t₂ k in
                                       (s , argt) ∷ args , target
takeArgs (el s (var x args)) (suc ())
takeArgs (el s (con c args)) (suc ())
takeArgs (el s (def f args)) (suc ())
takeArgs (el s (lam v t)) (suc ())
takeArgs (el s (pat-lam cs args)) (suc ())
takeArgs (el s (sort x)) (suc ())
takeArgs (el s (lit x)) (suc ())
takeArgs (el s unknown) (suc ())

getArgs : (t : Type) → Vec (Sort × Arg Type) (argCount t) × Type
getArgs t with takeArgs t (fromℕ (argCount t))
... | res rewrite to-from (argCount t) = res

addTakeArgs : ∀ t k → uncurry′ (addArgs ∘′ Data.Vec.toList) (takeArgs t k) ≡ t
addTakeArgs t zero = refl
addTakeArgs (el s (pi argt t₂)) (suc k) = cong (el s ∘′ pi argt) (addTakeArgs t₂ k)
addTakeArgs (el s (var x args)) (suc ())
addTakeArgs (el s (con c args)) (suc ())
addTakeArgs (el s (def f args)) (suc ())
addTakeArgs (el s (lam v t)) (suc ())
addTakeArgs (el s (pat-lam cs args)) (suc ())
addTakeArgs (el s (sort x)) (suc ())
addTakeArgs (el s (lit x)) (suc ())
addTakeArgs (el s unknown) (suc ())
