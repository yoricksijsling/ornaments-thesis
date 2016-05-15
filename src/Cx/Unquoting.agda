
module Cx.Unquoting where

open import Reflection
open import Common
open import Cx.Named
open import Cx.Quoting.QuotedDesc

-- we want a unquoteDatatypeᵐ which is kind of an inverse of quoteDatatypeᵐ
-- quoteDatatype : (`dt : Name) → TC (QuotedDesc Name)
-- unquoteDatatype : QuotedDesc Name → TC ⊤


-- module ConDescType {I : Cx₀}{Γ : Cx₁} (`dt : Name) where
module ConDescType {I : Cx₀}{Γ : Cx₁} (`dt : Type) where

  -- Takes a context Γ = (ε ▷ Sn ▷ .. ▷ S₂ ▷ S₁)
  -- and a term of type ⟦ Γ ⟧, `γ = `(((tt , vn) , .. , v₂) , v₁)
  -- Returns (top (popⁿ γ) ∷ .. ∷ top (pop γ) ∷ top γ ∷ [])
  -- (Equivalent to (vn ∷ .. ∷ v₂ ∷ v₁ ∷ [])
  cxLookupAll : ∀{a} → Cx {a} → Term → List (Arg (Term))
  cxLookupAll = helper
    where
    helper : ∀ Γ → Term → List (Arg (Term))
    helper (Γ ▷₁ S) `tm = helper Γ (def₁ (quote _▶₁_.pop) `tm) ++
                          [ vArg (def₁ (quote _▶₁_.top) `tm) ]
    helper (Γ ▷ S) `tm = helper Γ (def₁ (quote _▶₀_.pop) `tm) ++
                         [ vArg (def₁ (quote _▶₀_.top) `tm) ]
    helper ε `tm = []

  -- Given params and an instantiated context ((((tt , i₀) , i₁ ) , .. ) , ik)
  -- Returns something equivalent to `(Self p₀ p₁ .. pn i₀ i₁ .. ik)
  -- (Actually returns `(Self ps (top (popᵏ i)) .. (top (pop i)) (top i))
  selfRef : (params : List (Arg Term)) → (`i : Term) → Term
  selfRef params `i = foldl (λ f x → f `$ unArg x) `dt
                           (params ++ cxLookupAll I `i)

  -- p1 :: (p2 :: (p3 ..))
  -- ((`dt $ p1) $ p2) $ p3
  helper : ∀{Γ′} → (paramOffset : Nat) → (`γ : Term) → ConDesc I Γ′ → TC Type
  helper {Γ′} paramOffset `γ (ι o) =
    do `i ← quoteTC o >>= applyCx Γ′ `γ >>= forceTypeTC ⟦ I ⟧
    -| return (selfRef (cxVars paramOffset Γ) `i)
  helper {Γ′} paramOffset `γ (nm / S ⊗ xs) =
    do `tm ← quoteTC S >>= applyCx Γ′ `γ
    -| `rec ← helper (suc paramOffset)
                         (con₂ (quote _▶₀_._,_) (weaken 1 `γ) (var₀ 0))
                         xs
    -| return (pi (vArg `tm) (abs nm `rec))
  helper {Γ′} paramOffset `γ (nm /rec i ⊗ xs) =
    do `i ← quoteTC i >>= applyCx Γ′ `γ >>= forceTypeTC ⟦ I ⟧
    -| `rec ← helper (suc paramOffset) (weaken 1 `γ) xs
    -| return (pi (vArg (selfRef (cxVars paramOffset Γ) `i)) (abs nm `rec))

  -- Does not include parameters in the type, but does assume that they are in
  -- the context. The resulting type uses free variables.
  conDescTypeBare : ConDesc I Γ → TC Type
  conDescTypeBare D =
    do `tel ← cxToTel Γ
    -| inContext `tel (helper 0 (cxVal 0 Γ) D >>= normalise)

  -- Type of constructor including parameters
  conDescType : ConDesc I Γ → TC Type
  conDescType D = telPi <$> cxToTel Γ <*> helper 0 (cxVal 0 Γ) D >>= normalise
open ConDescType using (conDescTypeBare; conDescType) public

private
  postulate T0Self : Nat → Set
  t0 : ConDesc (ε ▷′ Nat) ε
  t0 = ι (λ γ → tt , 0)

  test-conDescType0 : giveT (conDescType (quoteTerm T0Self) t0) ≡ T0Self 0
  test-conDescType0 = refl

  postulate T1Self : Set → Nat → Set
  t1 : ConDesc (ε ▷′ Nat) (ε ▷₁′ Set)
  t1 = "n" / (λ γ → Nat) ⊗ "x" /rec (λ γ → (tt , 0)) ⊗ ι (λ γ → (tt , top γ))

  test-conDescType1 : giveT (conDescType (quoteTerm T1Self) t1) ≡
                      ((A : Set) (n : Nat) → T1Self A 0 → T1Self A n)
  test-conDescType1 = refl

  postulate T2Self : Nat → Bool → Set
  t2 : ConDesc (ε ▷′ Nat ▷′ Bool) ε
  t2 = ι (λ γ → (tt , 10) , true)
  test-conDescType2 : giveT (conDescType (quoteTerm T2Self) t2) ≡ T2Self 10 true
  test-conDescType2 = refl


IType : (I : Cx₀) → TC Type
IType I = cxToType set₀ I >>= normalise

IΓType : (I : Cx₀) (Γ : Cx₁) → TC Type
IΓType I Γ = flip telPi set₀ <$> (_++_ <$> cxToTel Γ <*> cxToTel I) >>= normalise

private
  test-IΓType : giveT (IΓType (ε ▷′ Nat) (ε ▷₁′ Set)) ≡ (Set → Nat → Set)
  test-IΓType = refl


module _ {I Γ #c} (D : DatDesc I Γ #c) where
  macro
    unquoteDat : Tactic
    unquoteDat = giveTC (IType I)

    unquoteCon : (k : Fin #c) → (`self : Term) → Tactic
    unquoteCon k `self = giveTC (conDescTypeBare `self (lookupCtor D k))



----------------------------------------
-- Dumping descriptions

-- Self is used as a placeholder in the types of the constructors
postulate
  Self : {X : Set₁} → X

PartS : Set
PartS = TC (List ErrorPart → List ErrorPart)
infixr 9 _<∘>_
_<∘>_ : PartS → PartS → PartS
_<∘>_ x y = _∘′_ <$> x <*> y

private
  str : String → PartS
  str s = return (_∷_ (strErr s))
  trm : Term → PartS
  trm t = return (_∷_ (termErr t))
  
  header : (`dt : Name) (I : Cx₀) (Γ : Cx₁) → PartS
  header `dt I Γ = str (showNameInModule `dt) <∘> str ":" <∘>
                   (IΓType I Γ >>= trm) <∘> str "\n"

  constr : ∀{I Γ} → (`dt : Name) → ConDesc I Γ → TC Type
  constr `dt D = conDescType (def₀ `dt) D

  constructors : ∀{I Γ #c} → (`dt : Name) →
                 (`cs : Vec (Name) #c) → DatDesc I Γ #c → PartS
  constructors `dt [] `0 = return id
  constructors `dt (`c ∷ `cs) (D ⊕ DS) = str (showNameInModule `c) <∘> str ":" <∘>
                                          (constr `dt D >>= trm) <∘>
                                          str "\n" <∘> constructors `dt `cs DS
  
  datatype : QuotedDesc → PartS
  datatype (mk {I} {Γ} `dt `cs desc) = header `dt I Γ <∘> constructors `dt `cs desc

dumpDatatype : QuotedDesc → TC ⊤
dumpDatatype D = datatype D >>= (λ f → typeError (f []))

macro
  dumpDatatypeᵐ : QuotedDesc → Tactic
  dumpDatatypeᵐ D = evalTC (dumpDatatype D)
