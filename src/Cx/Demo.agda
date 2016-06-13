
module Cx.Demo where

open import Common

module S where

  open import Cx.Simple


  natD : DatDesc 2
  natD = ι ⊕ (rec-⊗ ι) ⊕ `0

  natD-zero : μ natD
  natD-zero = ⟨ 0 , tt ⟩

  natD-suc : μ natD → μ natD
  natD-suc n = ⟨ 1 , n , tt ⟩


  listD : (A : Set) → DatDesc 2
  listD A = ι ⊕ ((λ γ → A) ⊗ rec-⊗ ι) ⊕ `0

  listD-nil : ∀{A} → μ (listD A)
  listD-nil = ⟨ 0 , tt ⟩

  listD-cons : ∀{A} → A → μ (listD A) → μ (listD A)
  listD-cons x xs = ⟨ 1 , x , xs , tt ⟩


  wrapFin : DatDesc 1
  wrapFin = (λ γ → Nat) ⊗ (λ γ → Fin (top γ)) ⊗ ι ⊕ `0



  module NatToList where
    nat→slist : DatOrn natD
    nat→slist = ι ⊕ ((λ δ → String) +⊗ rec-⊗ ι) ⊕ `0

    test-nat→slist : ornToDesc nat→slist ≡ listD String
    test-nat→slist = refl


    -- Using an ornamental algebra

    ex-list : μ (listD String)
    ex-list = listD-cons "Test" (listD-cons "one" (listD-cons "two" listD-nil))
    -- ex-list = ⟨ 1 , "Test" , ⟨ 1 , "one" , ⟨ 1 , "two" , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩ , tt ⟩

    forget-list : forget nat→slist ex-list ≡ natD-suc (natD-suc (natD-suc natD-zero))
    -- forget-list : forget nat→slist ex-list ≡ ⟨ 1 , ⟨ 1 , ⟨ 1 , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩ , tt ⟩
    forget-list = refl



module E where
  open import Cx.Extended

  natD : DatDesc ε ε 2
  natD = ι (λ _ → tt)
       ⊕ rec (λ _ → tt) ⊗ ι (λ _ → tt)
       ⊕ `0

  natD-zero : μ natD tt tt
  natD-zero = ⟨ 0 , refl ⟩

  natD-suc : μ natD tt tt → μ natD tt tt
  natD-suc n = ⟨ 1 , n , refl ⟩


  listD : DatDesc ε (ε ▷₁′ Set) 2
  listD = ι (λ _ → tt)
        ⊕ (λ γ → top γ) ⊗ rec (λ _ → tt) ⊗ ι (λ _ → tt)
        ⊕ `0
        
  listD-nil : ∀{A} → μ listD (tt , A) tt
  listD-nil = ⟨ 0 , refl ⟩
  
  listD-cons : ∀{A} → A → μ listD (tt , A) tt → μ listD (tt , A) tt
  listD-cons x xs = ⟨ 1 , x , xs , refl ⟩


  vecD : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
  vecD = ι (λ _ → tt , 0)
       ⊕ (λ _ → Nat) ⊗
         (top ∘ pop) ⊗
         rec (λ γ → tt , top (pop γ)) ⊗
         ι (λ γ → tt , suc (top (pop γ)))
       ⊕ `0


  module NatToList where
    -- Index stays ⊤. Parameters become (ε ▷₁′ Set).
    
    nat→list : Orn ε id (ε ▷₁′ Set) (λ _ → tt) natD
    nat→list = ι (λ δ → inv tt)
             ⊕ top +⊗ rec (λ δ → inv tt) ⊗ ι (λ δ → inv tt)
             ⊕ `0

    test-nat→list : ornToDesc nat→list ≡ listD
    test-nat→list = refl


  module ListToNatList where
    -- We can drop parameters using ornaments
    
    list-ex : μ listD (tt , Nat) tt
    list-ex = ⟨ 1 , 100 , ⟨ 1 , 33 , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩

    list→natlist : Orn ε id ε (λ x → x , Nat) listD
    list→natlist = ι (λ _ → inv tt)
                 ⊕ -⊗ rec (λ _ → inv tt) ⊗ ι (λ _ → inv tt)
                 ⊕ `0

    natlist-ex : μ (ornToDesc list→natlist) tt tt
    natlist-ex = ⟨ 1 , 100 , ⟨ 1 , 33 , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩


  module LengthAlgebra where
    lengthAlg : ∀ {A} → Alg listD (tt , A) (λ tt → Nat)
    lengthAlg (zero , refl) = 0
    lengthAlg (suc zero , x , xs , refl) = suc xs
    lengthAlg (suc (suc ()) , _)

    list→vec : Orn (ε ▷′ Nat) (λ _ → tt) (ε ▷₁′ Set) id listD
    list→vec = algOrn lengthAlg

    vecD′ : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
    vecD′ = ι (λ _ → (tt , 0))
          ⊕ top ⊗
             (λ _ → Nat) ⊗
             rec (λ γ → tt , top γ) ⊗
             ι (λ γ → tt , suc (top γ))
          ⊕ `0

    test-list→vec : ornToDesc list→vec ≡ vecD′
    test-list→vec = refl


  module ReornamentNatToList where
    open NatToList

    nat→vec : Orn (ε ▷ (λ γ → μ natD tt tt)) (λ _ → tt) (ε ▷₁′ Set) (λ _ → tt) natD
    nat→vec = reornament nat→list

    vecD′ : DatDesc (ε ▷ (λ γ → μ natD tt tt)) (ε ▷₁′ Set) 2
    vecD′ = ι (λ _ → (tt , natD-zero))
          ⊕ top ⊗
            (λ _ → μ natD tt tt) ⊗
            rec (λ γ → tt , top γ) ⊗
            ι (λ γ → tt , natD-suc (top γ))
          ⊕ `0

    test-nat→vec : ornToDesc nat→vec ≡ vecD′
    test-nat→vec = refl

    ex-vec : μ (ornToDesc nat→vec) (tt , Nat) (tt , (natD-suc (natD-suc natD-zero)))
    ex-vec = ⟨ 1 , 33 , _ , ⟨ 1 , 44 , _ , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩

    test-forget-vec : forget nat→vec ex-vec ≡ natD-suc (natD-suc natD-zero)
    test-forget-vec = refl


module N where
  open import Cx.HasDesc
  open import Cx.Quoting
  open import Cx.GenericOperations
  open import Reflection

  module QuoteNat where

    unquoteDecl quotedNat natHasDesc =
      deriveHasDesc quotedNat natHasDesc (quote Nat)

    natDesc : DatDesc ε ε 2
    natDesc = QuotedDesc.desc quotedNat

    test-desc : natDesc ≡
      ( ι (λ _ → tt)
      ⊕ "n" /rec (λ _ → tt) ⊗ ι (λ _ → tt)
      ⊕ `0 )
    test-desc = refl

    test-dtname : quotedNat ≡ mk (quote Nat) (quote Nat.zero ∷ quote Nat.suc ∷ []) natDesc
    test-dtname = refl


  module ListHasDesc where

    listDesc : DatDesc ε (ε ▷₁′ Set) 2
    listDesc = ( ι (λ _ → tt)
            ⊕ "x" / top ⊗ "xs" /rec (λ _ → tt) ⊗ ι (λ _ → tt)
            ⊕ `0 )

    listTo : ∀{A} → List A → μ listDesc (tt , A) tt
    listTo [] = ⟨ 0 , refl ⟩
    listTo (x ∷ xs) = ⟨ 1 , x , listTo xs , refl ⟩

    listFrom : ∀{A} → μ listDesc (tt , A) tt → List A
    listFrom ⟨ zero , refl ⟩ = []
    listFrom ⟨ suc zero , x , xs , refl ⟩ = x ∷ listFrom xs
    listFrom ⟨ suc (suc ()) , _ ⟩

    instance
      listHasDesc : ∀{A} → HasDesc (List A)
      listHasDesc = mk listDesc listTo listFrom

    list-ex : List Nat
    list-ex = 10 ∷ 20 ∷ 30 ∷ []

    test-list-depth : gdepth list-ex ≡ 3
    test-list-depth = refl


  module QuoteList where

    data MyList (A : Set) : Set where
      nil : MyList A
      cons : (x : A) → (xs : MyList A) → MyList A

    unquoteDecl quotedList listHasDesc =
      deriveHasDesc quotedList listHasDesc (quote MyList)

    listDesc : DatDesc ε (ε ▷₁′ Set) 2
    listDesc = QuotedDesc.desc quotedList

    test-desc : listDesc ≡
      ( ι (λ _ → tt)
      ⊕ "x" / top ⊗ "xs" /rec (λ _ → tt) ⊗ ι (λ _ → tt)
      ⊕ `0 )
    test-desc = refl

    ex-list : MyList Bool
    ex-list = cons true $ cons false $ cons true nil
    ex-to : to ex-list ≡ ⟨ 1 , true
                             , ⟨ 1 , false
                                   , ⟨ 1 , true
                                         , ⟨ zero , refl ⟩
                                         , refl ⟩
                                   , refl ⟩
                             , refl ⟩
    ex-to = refl

    myLength′ : ∀{A} → MyList A → Nat
    myLength′ nil = 0
    myLength′ (cons x xs) = suc (myLength′ xs)

    myLength : ∀{A} → MyList A → Nat
    myLength = gdepth

    test-length : ∀{A} → (xs : MyList A) → myLength xs ≡ myLength′ xs
    test-length nil = refl
    test-length (cons x xs) = cong suc (test-length xs)

  module NatToList where
    open import Cx.Conversions
    open QuoteNat
    open QuoteList

    nat→list : Orn _ _ natDesc
    nat→list = renameArguments 1 (just "xs" ∷ [])
           >>⁺ addParameterArg 1 "x"

    listDescByOrnament : DatDesc ε (ε ▷₁′ Set) 2
    listDescByOrnament = ornToDesc nat→list

    test-nat→list : listDescByOrnament ≡ listDesc
    test-nat→list = refl

    nat→list′ : DefOrn ε id (ε ▷₁′ Set) (λ _ → tt) natDesc
    nat→list′ = ι (λ _ → inv tt)
              ⊕ "x" / top +⊗ "xs" /rec (λ _ → inv tt) ⊗ (ι (λ _ → inv tt))
              ⊕ `0
    test-nat→list′ : nat→list′ ≡ nat→list
    test-nat→list′ = refl

    -- Without renaming the other argument
    nat→list-without-renaming : ornToDesc (addParameterArg {D = natDesc} 1 "x") ≡ⁿ listDesc
    nat→list-without-renaming = refl

    -- a = {!evalT (quoteDatatypeTo (quote MyList) listDescByOrnament)!}


  module NatToListByDepth where
    open QuoteList

    list→vec : Orn _ _ listDesc
    list→vec = algOrn (depthAlg listDesc)

    vecD′ : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
    vecD′ = ι (λ _ → tt , 0)
          ⊕ "x" / top ⊗
            "_" / (λ γ → Nat) ⊗
            "xs" /rec (λ γ → tt , top γ) ⊗
            ι (λ γ → tt , suc (top γ))
          ⊕ `0

    test-list→vec : ornToDesc list→vec ≡ vecD′
    test-list→vec = refl



  module QuoteVec where
    vecDesc : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
    vecDesc = ι (λ _ → tt , 0)
         ⊕ "n" / (λ γ → Nat)
                  ⊗ "x" / (λ γ → top (pop γ))
                  ⊗ "xs" /rec (λ γ → tt , top (pop γ))
                  ⊗ ι (λ γ → tt , suc (top (pop γ)))
         ⊕ `0

    data MyVec (A : Set) : Nat → Set where
      nil : MyVec A 0
      cons : ∀ n → (x : A) → (xs : MyVec A n) → MyVec A (suc n)

    unquoteDecl quotedVec vecHasDesc =
      deriveHasDesc quotedVec vecHasDesc (quote MyVec)

    test-desc : QuotedDesc.desc quotedVec ≡ vecDesc
    test-desc = refl

    open import Cx.Unquoting

    -- dn = dumpDatatypeᵐ quotedVec

    data UVec (A : Set) : unquoteDat vecDesc where
      nil : unquoteCon vecDesc 0 UVec
      cons : unquoteCon vecDesc 1 UVec


  module MultiIndex where
    -- Limitation: Indices can not depend on parameters
    data Multi : (n : Nat) → Fin n → Set where
      fo : (n : Nat) → (k : Fin n) → Multi n k
    data MultiP (A : Set) : (n : Nat) → Vec A n → Set where
      fo : (n : Nat) → (xs : Vec A n) → MultiP A n xs

    q : QuotedDesc
    q = evalT (quoteDatatype (quote Multi))

    open import Reflection using (ShouldFailᵐ)
    qp : ShouldFailᵐ (quoteDatatype (quote MultiP))
    qp = tt
