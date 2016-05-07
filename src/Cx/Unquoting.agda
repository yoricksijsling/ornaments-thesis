
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
  `pop^ : ∀{tp} → Nat → ⟦ tp ⟧tp → ⟦ tp ⟧tp
  `pop^ zero x = x
  `pop^ (suc n) x = `con₁ (quote pop) (`pop^ n x)

  `top-pops : Nat → Term → List (Arg (Term))
  `top-pops zero tm = []
  `top-pops (suc n) tm = let a = def (quote top) (hArg (quoteTerm (lsuc lzero)) ∷
                                                  vArg (`pop^ n tm) ∷ [])
                         in vArg a ∷ `top-pops n tm

  -- Given params and an instantiated context ((((tt , i₀) , i₀ ) , .. ) , in)
  -- Returns something equivalent to `(Self p₀ p₁ .. pn i₀ i₁ .. in)
  -- (Actually returns (λ i → `Self p₀ p₁ .. pn (top (popᵏ i)) .. (top (pop i)) (top i)) i)
  selfRef : (params : List (Arg Term)) → (i : Term) → Term
  -- selfRef params i = def `dt (params ++ `top-pops (CxLength I) i)
  selfRef params i = foldl (λ f x → f `$ unArg x) `dt
                           (params ++ `top-pops (CxLength I) i)

  -- p1 :: (p2 :: (p3 ..))
  -- ((`dt $ p1) $ p2) $ p3
  helper : ∀{Γ′} → (paramOffset : Nat) → (`γ : Term) → ConDesc I Γ′ → TC Type
  helper {Γ′} paramOffset `γ (ι o) =
    do `i ← quoteTC o >>= applyCx Γ′ `γ
    -| return (selfRef (cxVars paramOffset Γ) `i)
  helper {Γ′} paramOffset `γ (nm / S ⊗ xs) =
    do `tm ← quoteTC S >>= applyCx Γ′ `γ
    -| `rec ← helper (suc paramOffset)
                         (con₂ (quote _▶₀_._,_) (weaken 1 `γ) (var₀ 0))
                         xs
    -| return (pi (vArg `tm) (abs nm `rec))
  helper {Γ′} paramOffset `γ (nm /rec i ⊗ xs) =
    do `i ← quoteTC i >>= applyCx Γ′ `γ
    -| `rec ← helper (suc paramOffset) (weaken 1 `γ) xs
    -| return (pi (vArg (selfRef (cxVars paramOffset Γ) `i)) (abs nm `rec))

  -- Does not include parameters in the type, but does assume that they are in
  -- the context. Because it uses free variables the type is not self-contained
  -- and can not be normalised or unquoted.
  conDescTypeBare : ConDesc I Γ → TC Type
  conDescTypeBare D = helper 0 (cxVal 0 Γ) D

  -- Type of constructor including parameters
  conDescType : ConDesc I Γ → TC Type
  conDescType D = telPi <$> cxToTel Γ <*> conDescTypeBare D >>= normalise
open ConDescType using (conDescTypeBare; conDescType) public

IType : (I : Cx₀) → TC Type
IType I = cxToType set₀ I >>= normalise

IΓType : (I : Cx₀) (Γ : Cx₁) → TC Type
IΓType I Γ = flip telPi set₀ <$> (_++_ <$> cxToTel Γ <*> cxToTel I) >>= normalise

private
  postulate CdSelf : Set → Nat → Set
  cd : ConDesc (ε ▷′ Nat) (ε ▷₁′ Set)
  cd = "n" / (λ γ → Nat) ⊗ "x" /rec (λ γ → (tt , 0)) ⊗ ι (λ γ → (tt , top γ))

  test-conDescType : giveT (conDescType (quoteTerm CdSelf) cd) ≡
                   ((A : Set) (n : Nat) → CdSelf A 0 → CdSelf A n)
  test-conDescType = refl

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

DumpableName : Bool → Set
DumpableName true = Name
DumpableName false = String

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

  nameAsString : ∀{b} → DumpableName b → String
  nameAsString {false} n = n
  nameAsString {true} n = showNameInModule n
  
  header : ∀{b} (`dt : DumpableName b) (I : Cx₀) (Γ : Cx₁) → PartS
  header `dt I Γ = str (nameAsString `dt) <∘> str ":" <∘>
                   (IΓType I Γ >>= trm) <∘> str "\n"

  constr : ∀{b I Γ} → (`dt : DumpableName b) → ConDesc I Γ → TC Type
  constr {false} {I} {Γ} `dt D = IΓType I Γ >>= λ `dty →
                                 conDescType (def (quote Self) [ hArg `dty ]) D
  constr {true} `dt D = conDescType (def₀ `dt) D

  constructors : ∀{b I Γ #c} → (`dt : DumpableName b) →
                 (`cs : Vec (DumpableName b) #c) → DatDesc I Γ #c → PartS
  constructors `dt [] `0 = return id
  constructors `dt (`c ∷ `cs) (D ⊕ DS) = str (nameAsString `c) <∘> str ":" <∘>
                                          (constr `dt D >>= trm) <∘>
                                          str "\n" <∘> constructors `dt `cs DS
  
  datatype : ∀{b} → QuotedDesc (DumpableName b) → PartS
  datatype (mk {I} {Γ} `dt `cs desc) = header `dt I Γ <∘> constructors `dt `cs desc

dumpDatatype : ∀{b} → QuotedDesc (DumpableName b) → TC ⊤
dumpDatatype D = datatype D >>= (λ f → typeError (f []))

macro
  dumpDatatypeᵐ : ∀{b} → QuotedDesc (DumpableName b) → Tactic
  dumpDatatypeᵐ D = evalTC (dumpDatatype D)
