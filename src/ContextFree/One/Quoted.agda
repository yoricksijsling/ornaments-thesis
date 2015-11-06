module ContextFree.One.Quoted where

open import Reflection
open import Data.List using (List)
open import Data.Product using (_×_)

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
    params : List (Sort × Arg Type)
    sop : SafeSum

