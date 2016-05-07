
module Cx.Quoting where

open import Reflection
open import Common
open import Cx.Named public
open import Cx.Quoting.Constructor
open import Cx.Quoting.QuotedDesc

quoteConstructors : (`dt : Name) (#p : Nat) → ∀ I Γ → (cnames : List Name) →
                    TC (DatDesc I Γ (length cnames))
quoteConstructors `dt #p I Γ [] = return `0
quoteConstructors `dt #p I Γ (cname ∷ cnames) =
  do c ← quoteConstructor `dt #p I Γ cname
  -| cs ← quoteConstructors `dt #p I Γ cnames
  -| return (c ⊕ cs)

quoteDatatype : (`dt : Name) → TC (QuotedDesc Name)
quoteDatatype `dt =
  do dttype ← getType `dt
  =| #p ← getParameters `dt
  =| I ← typeToCx #p nothing dttype
  =| Γ ← typeToCx 0 (just #p) dttype
  =| `cnames ← getConstructors `dt
  =| datdesc ← quoteConstructors `dt #p I Γ `cnames
  =| return (mk `dt (listToVec `cnames) datdesc)

private
  tcEq : ∀{a}{A : Set a} → (x y : A) → TC (x ≡ y)
  tcEq x y = catchTC (unquoteTC (con₀ (quote _≡_.refl))) $
    quoteTC x >>=′ λ `x → quoteTC y >>=′ λ `y →
    typeError (strErr "tcEq:" ∷ termErr `x ∷
               strErr "does not equal" ∷ termErr `y ∷ [])

-- Connect a Desc to an existing datatype
-- quoteDatatype, decide if quoted desc is equal to given desc,
-- replace quoted desc by given desc
quoteDatatypeTo : (`dt : Name) → ∀{I Γ #c} → DatDesc I Γ #c → TC (QuotedDesc Name)
quoteDatatypeTo `dt {I} {Γ} {#c} D =
  do dw ← quoteDatatype `dt
  =| Ieq ← tcEq I (QuotedDesc.I dw)
  =| Γeq ← tcEq Γ (QuotedDesc.Γ dw)
  =| #ceq ← tcEq #c (QuotedDesc.#c dw)
  =| D′ := transport id (DatDesc $≡ Ieq *≡ Γeq *≡ #ceq) D
  -| _ ← tcEq D′ (QuotedDesc.desc dw)
  =| return (mk (QuotedDesc.`datatypeName dw) (QuotedDesc.`constructorNames dw) D′)
