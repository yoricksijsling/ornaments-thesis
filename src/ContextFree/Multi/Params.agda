module ContextFree.Multi.Params where

open import Common
open import Reflection
open import Stuff using (zipNatsDown)
open import Tactic.Nat

pattern arg-pat a s t = pi (arg (arg-info visible relevant) a) (abs s t)

data ArgView : Type → Set where
  arg : (a : Type)(s : String)(t : Type) → ArgView (arg-pat a s t)
  rest : (t : Type) → ArgView t

argView : (t : Type) → ArgView t
argView (arg-pat a s t) = arg a s t
argView t = rest t

getArgs : (t : Type) → List Type × Type
getArgs t with argView t
getArgs ._ | arg a _ t = map× (_∷_ a) id (getArgs t)
getArgs ._ | rest t = [] , t


data Param : Set where
  param₀ : (v : Visibility)(s : String) → Param
  paramx : (v : Visibility)(s : String)(ty : Type) → Param

pattern param₀-pat v s r = pi (arg (arg-info v relevant) set₀) (abs s r)
pattern paramx-pat v s ty r = pi (arg (arg-info v relevant) ty) (abs s r)

data ParamView : Type → Set where
  param₀ : (v : Visibility)(s : String)(r : Type) → ParamView (param₀-pat v s r)
  paramx : (v : Visibility)(s : String)(ty : Type)(r : Type) → ParamView (paramx-pat v s ty r)
  rest : (t : Type) → ParamView t

paramView : (t : Type) → ParamView t
paramView (param₀-pat v s r) = param₀ v s r
paramView (paramx-pat v s ty r) = paramx v s ty r
paramView t = rest t

paramCount : Type → Nat
paramCount t with paramView t
paramCount ._ | param₀ v s r = suc (paramCount r)
paramCount ._ | paramx v s ty r = suc (paramCount r)
paramCount ._ | rest t = 0

takeParams : (t : Type)(n : Nat){{p : IsTrue (lessNat n (suc (paramCount t)))}} → Vec Param n × Type
takeParams t zero = [] , t
takeParams t (suc n) {{p}} with paramView t
takeParams ._ (suc n) | param₀ v s r = map× (_∷_ (param₀ v s)) id (takeParams r n)
takeParams ._ (suc n) | paramx v s ty r = map× (_∷_ (paramx v s ty)) id (takeParams r n)
takeParams ._ (suc n) {{}} | rest t

-- Takes (p₁,p₂,..,pn) and some type `T` to `p₁ → p₂ → .. → pn → T`
addParams : List Param → Type → Type
addParams [] target = target
addParams (param₀ v s ∷ args) target = param₀-pat v s (addParams args target)
addParams (paramx v s ty ∷ args) target = paramx-pat v s ty (addParams args target)

dropParams : (t : Type)(n : Nat) → Maybe Type
dropParams t zero = just t
dropParams t (suc n) with paramView t
dropParams ._ (suc n) | param₀ v s r = dropParams r n
dropParams ._ (suc n) | paramx v s ty r = dropParams r n
dropParams ._ (suc n) | rest t = nothing

-- Takes (p₁,p₂,..,pn) and some term `T` to `λ p₁ p₂ .. pn → T`
addParamsTm : List Param → Term → Term
addParamsTm [] target = target
addParamsTm (param₀ v s ∷ ps) target = lam v (abs s (addParamsTm ps target))
addParamsTm (paramx v s ty ∷ ps) target = lam v (abs s (addParamsTm ps target))

module _ where
  addTakeParams : ∀ t n p → uncurry′ (addParams ∘ vecToList) (takeParams t n {{p}}) ≡ t
  addTakeParams t zero p = refl
  addTakeParams t (suc n) p with paramView t
  addTakeParams ._ (suc n) p | param₀ v s r = cong (param₀-pat v s) (addTakeParams r n p)
  addTakeParams ._ (suc n) p | paramx v s ty r = cong (paramx-pat v s ty) (addTakeParams r n p)
  addTakeParams ._ (suc n) () | rest t


paramVars : ∀{tp}(offset : Nat){pc : Nat} → Vec Param pc → List (Arg ⟦ tp ⟧tp)
paramVars {tp} offset = zipNatsDown offset tm ∘ vecToList
  where tm : Nat → Param → Arg ⟦ tp ⟧tp
        tm offset (param₀ v s) = arg (arg-info v relevant) (`var₀ offset s)
        tm offset (paramx v s ty) = arg (arg-info v relevant) (`var₀ offset s)

paramPats : {pc : Nat} → Vec Param pc → List (Arg Pattern)
paramPats = paramVars 0 -- If it is used as a pattern, the offset is ignored

module _ where
  test-paramVars-t : paramVars {tp-term} 1 (param₀ visible "a" ∷ param₀ visible "b" ∷ [])
                   ≡ vArg (var 2 []) ∷ vArg (var 1 []) ∷ []
  test-paramVars-t = refl

  test-paramVars-p : paramVars {tp-patt} 1 (param₀ visible "a" ∷ param₀ visible "b" ∷ [])
                   ≡ vArg (var "a") ∷ vArg (var "b") ∷ []
  test-paramVars-p = refl
