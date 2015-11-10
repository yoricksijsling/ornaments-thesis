module ContextFree.One.Quoted where

open import Reflection
open import Data.List using (List)
open import Data.Product using (_×_)

Params : Set
Params = List (Sort × Arg Type)

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
    dtname : Name
    params : Params
    sop : SafeSum

