
module Cx.Demo where

open import Common

module S where

  open import Cx.Simple.Ornament


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



  module Nat→List where
    nat→slist : DatOrn natD
    nat→slist = ι ⊕ (insert (λ δ → String) ⊗ rec-⊗ ι) ⊕ `0

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
  open import Cx.Extended.AlgebraicOrnament
  
  natD : DatDesc ⊤ ε 2
  natD = ι (λ _ → tt)
         ⊕ rec (λ _ → tt) ⊗ ι (λ _ → tt)
         ⊕ `0

  natD-zero : μ natD tt tt
  natD-zero = ⟨ 0 , refl ⟩

  natD-suc : μ natD tt tt → μ natD tt tt
  natD-suc n = ⟨ 1 , n , refl ⟩


  listD : DatDesc ⊤ (ε ▷₁ (λ γ → Set)) 2
  listD = ι (λ _ → tt)
        ⊕ (λ γ → top γ) ⊗ rec (λ _ → tt) ⊗ ι (λ _ → tt)
        ⊕ `0
        
  listD-nil : ∀{A} → μ listD (tt , A) tt
  listD-nil = ⟨ 0 , refl ⟩
  
  listD-cons : ∀{A} → A → μ listD (tt , A) tt → μ listD (tt , A) tt
  listD-cons x xs = ⟨ 1 , x , xs , refl ⟩


  vecD : DatDesc Nat (ε ▷₁ (λ γ → Set)) 2
  vecD = ι (λ _ → 0)
       ⊕ (λ _ → Nat) ⊗ (top ∘ pop) ⊗ rec (top ∘ pop) ⊗ ι (suc ∘ top ∘ pop)
       ⊕ `0


  module NatToList where
    -- Index stays ⊤. Parameters become (ε ▷₁ (λ γ → Set)).
    
    nat→list : DefOrn ⊤ id (ε ▷₁ (λ γ → Set)) (mk (λ _ → tt)) natD
    nat→list = ι (λ δ → inv tt)
             ⊕ insert top ⊗ rec (λ δ → inv tt) ⊗ ι (λ δ → inv tt)
             ⊕ `0

    test-nat→list : ornToDesc nat→list ≡ listD
    test-nat→list = refl


  module ListToNatList where
    -- We can drop parameters using ornaments
    
    list-ex : μ listD (tt , Nat) tt
    list-ex = ⟨ 1 , 100 , ⟨ 1 , 33 , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩

    list→natlist : DefOrn ⊤ id ε (mk (λ x → x , Nat)) listD
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

    list→vec : DefOrn (⊤ × Nat) fst (ε ▷₁ (λ γ → Set)) (cxf-id _) listD
    list→vec = algOrn listD lengthAlg

    vecD′ : DatDesc (⊤ × Nat) (ε ▷₁ (λ γ → Set)) 2
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

    nat→vec : DefOrn (⊤ × μ natD tt tt) fst (ε ▷₁ (λ γ → Set)) (mk (λ _ → tt)) natD
    nat→vec = reornament nat→list

    vecD′ : DatDesc (⊤ × μ natD tt tt) (ε ▷₁ (λ γ → Set)) 2
    vecD′ = ι (λ _ → (tt , natD-zero))
          ⊕ top ⊗ (λ _ → μ natD tt tt) ⊗ rec (λ γ → tt , top γ) ⊗ ι (λ γ → tt , natD-suc (top γ))
          ⊕ `0

    test-nat→vec : ornToDesc nat→vec ≡ vecD′
    test-nat→vec = refl

    ex-vec : μ (ornToDesc nat→vec) (tt , Nat) (tt , (natD-suc (natD-suc natD-zero)))
    ex-vec = ⟨ 1 , 33 , _ , ⟨ 1 , 44 , _ , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩

    test-forget-vec : forget nat→vec ex-vec ≡ natD-suc (natD-suc natD-zero)
    test-forget-vec = refl


module N where
  open import Cx.Named
  open import Cx.Quotable.Core
  open import Cx.Quoting
  
  module QuoteNat where

    natD : DatDesc ⊤ ε 2
    natD = ι (λ _ → tt)
         ⊕ "n" /rec (λ _ → tt) ⊗ ι (λ _ → tt)
         ⊕ `0

    q : QuotedDesc
    q = quoteDatatypeᵐ Nat

    test-desc : QuotedDesc.desc q ≡ natD
    test-desc = refl

    test-dtname : q ≡ mk (quote Nat) (quote Nat.zero ∷ quote Nat.suc ∷ []) natD
    test-dtname = refl


  module QuoteList where

    listD : DatDesc ⊤ (ε ▷₁ (λ _ → Set)) 2
    listD = ι (λ _ → tt)
          ⊕ "x" / top ⊗ "xs" /rec (λ _ → tt) ⊗ ι (λ _ → tt)
          ⊕ `0

    data PList (A : Set) : Set where
      nil : PList A
      cons : (x : A) → (xs : PList A) → PList A

    q : QuotedDesc
    q = quoteDatatypeᵐ PList

    test-desc : QuotedDesc.desc q ≡ listD
    test-desc = refl


  module NatToList where

    nat→list : DefOrn ⊤ id (ε ▷₁ (λ _ → Set)) (mk (λ _ → tt)) QuoteNat.natD
    nat→list = ι (λ _ → inv tt)
             ⊕ "x" / top +⊗ "xs" /rec (λ _ → inv tt) ⊗ (ι (λ _ → inv tt))
             ⊕ `0

    test-nat→list : ornToDesc nat→list ≡ QuoteList.listD
    test-nat→list = refl


  module QuoteVec where
    vecD : DatDesc (Nat × ⊤) (ε ▷₁ (λ γ → Set)) 2
    vecD = ι (λ _ → 0 , tt)
         ⊕ "n" / (λ γ → Nat)
                  ⊗ "x" / (λ γ → top (pop γ))
                  ⊗ "xs" /rec (λ γ → top (pop γ) , tt)
                  ⊗ ι (λ γ → suc (top (pop γ)) , tt)
         ⊕ `0

    data MyVec (A : Set) : Nat → Set where
      nil : MyVec A 0
      cons : ∀ n → (x : A) → (xs : MyVec A n) → MyVec A (suc n)

    q : QuotedDesc
    q = quoteDatatypeᵐ MyVec

    test-desc : QuotedDesc.desc q ≡ vecD
    test-desc = refl


