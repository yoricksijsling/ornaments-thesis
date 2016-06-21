
module Thesis.Extended where

open import Common
open import Cx.Extended hiding (⟦_⟧desc; fold)

{-# TERMINATING #-}
⟦_⟧desc : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → (⟦ I ⟧ → Set) → (⟦ I ⟧ → Set)
⟦_⟧desc {dt = isCon} (ι o′) γ X o = o′ γ ≡ o
⟦_⟧desc {dt = isCon} (S ⊗ xs) γ X o = Σ (S γ) λ s → ⟦ xs ⟧desc (γ , s) X o
⟦_⟧desc {dt = isCon} (rec i ⊗ xs) γ X o = X (i γ) × ⟦ xs ⟧desc γ X o
⟦_⟧desc {dt = isDat #c} D γ X o = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧desc γ X o

{-# TERMINATING #-}
fold : ∀{I Γ #c}{D : DatDesc I Γ #c}{γ X} (α : Alg D γ X) →
       μ D γ →ⁱ X
fold {D = D} α ⟨ xs ⟩ = α (descmap (fold α) D xs)


--------------------
-- Descriptions

listDesc : DatDesc ε (ε ▷₁′ Set) 2
listDesc = ι (const tt)
  ⊕ top ⊗ rec (const tt) ⊗ ι (const tt)
  ⊕ `0

list-to : ∀{A} → List A → μ listDesc (tt , A) tt
list-to [] = ⟨ 0 , refl ⟩
list-to (x ∷ xs) = ⟨ 1 , x , list-to xs , refl ⟩

{-
data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} (i : Fin n) → Fin (suc n)

finDesc : DatDesc (ε ▷′ Nat) ε 2
finDesc = const Nat ⊗ ι {!!}
  ⊕ const Nat ⊗ rec {!!} ⊗ ι {!!}
  ⊕ `0

data FinTT (A : ⟦ ε ⟧) : ⟦ ε ▷′ Nat ⟧ → Set where
  zero : (n : Nat) → FinTT A {!!}
  suc : (n : Nat) (i : FinTT A {!!}) → FinTT A {!!}
-}

data FinTT (A : ⟦ ε ⟧ ofType Set₁) : (⟦ ε ▷′ Nat ⟧ ofType Set₁) → Set where
  zero : (n : Nat) → FinTT A (tt , suc n)
  suc : (n : Nat) (i : FinTT A (tt , n)) → FinTT A (tt , suc n)

finDesc : DatDesc (ε ▷′ Nat) ε 2
finDesc = const Nat ⊗ ι (λ γ → tt , suc (top γ))
  ⊕ const Nat ⊗ rec (λ γ → tt , top γ) ⊗ ι (λ γ → tt , suc (top γ))
  ⊕ `0

{-
fin-zero′ : μ finDesc tt (tt , 10)
fin-zero′ = ⟨ 0 , ?0 , ?1 ⟩
-- |?0| : Nat
-- |?1| : (tt , suc ?0) ≡ (tt , 10)
-}

fin-zero : μ finDesc tt (tt , 10)
fin-zero = ⟨ 0 , 9 , refl ⟩

fintt-zero : FinTT tt (tt , 10)
fintt-zero = zero 9

--------------------

sumAlg : Alg listDesc (tt , Nat) (const Nat)
sumAlg (zero , refl) = 0
sumAlg (suc zero , x , xs , refl) = x + xs
sumAlg (suc (suc ()) , _)

lengthAlg : {A : Set} → Alg listDesc (tt , A) (const Nat)
lengthAlg (zero , refl) = 0
lengthAlg (suc zero , x , xs , refl) = suc xs
lengthAlg (suc (suc ()) , _)

--------------------

fin-to : ∀{n} → Fin n → μ finDesc tt (tt , n)
fin-to zero = ⟨ 0 , _ , refl ⟩
fin-to (suc k) = ⟨ 1 , _ , fin-to k , refl ⟩
fin-from : ∀{n} → μ finDesc tt (tt , n) → Fin n
fin-from ⟨ zero , _ , refl ⟩ = zero
fin-from ⟨ suc zero , _ , k , refl ⟩ = suc (fin-from k)
fin-from ⟨ suc (suc ()) , _ ⟩

raiseAlg : (m : Nat) → Alg finDesc tt (λ i → μ finDesc tt (tt , top i + m))
raiseAlg m (zero , n , refl) = ⟨ 0 , n + m , refl ⟩
raiseAlg m (suc zero , n , k , refl) = ⟨ 1 , n + m , k , refl ⟩
raiseAlg m (suc (suc ()) , _)

raise : ∀{n} → (m : Nat) → Fin n → Fin (n + m)
raise m = fin-from ∘ fold (raiseAlg m) ∘ fin-to

f2<5 : Fin 5
f2<5 = suc (suc zero)

f2<9 : Fin 9
f2<9 = raise 4 f2<5

check-f2<9 : f2<9 ≡ suc (suc zero)
check-f2<9 = refl


--------------------
-- Ornaments

{-
list→vec : Orn (ε ▷′ Nat) (λ _ → tt) (ε ▷₁′ Set) id listDesc
list→vec = ι {!!}
  ⊕ const Nat +⊗ -⊗ rec {!!} ⊗ ι {!!}
  ⊕ `0

-- |?0 : (δ : ⊤′ ▶₁ const Set) → (λ _ → tt) ⁻¹ tt|
-- |?1 : (δ : ⊤′ ▶₁ const Set ▶₀ const Nat ▶₀ top ∘ pop) → (λ j → tt) ⁻¹ tt|
-- |?2 : (δ : ⊤′ ▶₁ const Set ▶₀ const Nat ▶₀ top ∘ pop) → (λ j → tt) ⁻¹ tt|
-}

list→vec : Orn (ε ▷′ Nat) (λ j → tt) (ε ▷₁′ Set) id listDesc
list→vec = ι (λ δ → inv (tt , 0))
  ⊕ const Nat +⊗ -⊗ rec (λ δ → inv (tt , top (pop δ)))
  ⊗ ι (λ δ → inv (tt , suc (top (pop δ))))
  ⊕ `0

vecDesc : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
vecDesc = ornToDesc list→vec

vec-to : ∀{A n} → Vec A n → μ vecDesc (tt , A) (tt , n)
vec-to [] = ⟨ 0 , refl ⟩
vec-to (x ∷ xs) = ⟨ 1 , _ , x , vec-to xs , refl ⟩

-- copyAlg?


--------------------
-- Algebraic ornaments

list→vec₁ : Orn (ε ▷ const Nat) pop (ε ▷₁′ Set) id listDesc
list→vec₁ = algOrn listDesc lengthAlg

vecDesc₁ : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
vecDesc₁ = ι (const (tt , 0))
  ⊕ top
  ⊗ const Nat
  ⊗ rec (λ γ → tt , top γ)
  ⊗ ι (λ γ → tt , suc (top γ))
  ⊕ `0

test-list→vec₁ : ornToDesc list→vec₁ ≡ vecDesc₁
test-list→vec₁ = refl


--------------------
-- Reornament

{-
postulate
  reornament′ : ∀{I J u Δ Γ}{c : Cxf Δ Γ}{#c}{D : DatDesc I Γ #c} →
    (o : Orn J u Δ c D) → Orn (J ▷ μ D (c {!!}) ∘ u) (u ∘ pop) Δ c D
-}

natDesc : DatDesc ε ε 2
natDesc = ι (λ _ → tt)
  ⊕ rec (λ _ → tt) ⊗ ι (λ _ → tt)
  ⊕ `0
natDesc-zero : μ natDesc tt tt
natDesc-zero = ⟨ 0 , refl ⟩
natDesc-suc : μ natDesc tt tt → μ natDesc tt tt
natDesc-suc n = ⟨ 1 , n , refl ⟩

nat→list : Orn ε id (ε ▷₁′ Set) (λ δ → tt) natDesc
nat→list = ι (λ δ → inv tt)
  ⊕ top +⊗ rec (λ δ → inv tt) ⊗ ι (λ δ → inv tt)
  ⊕ `0

nat→vec₂ : Orn (ε ▷′ μ natDesc tt tt) (λ j → tt) (ε ▷₁′ Set) (λ δ → tt) natDesc
nat→vec₂ = reornament nat→list

vecDesc₂ : DatDesc (ε ▷′ μ natDesc tt tt) (ε ▷₁′ Set) 2
vecDesc₂ = ι (const (tt , natDesc-zero))
  ⊕ top
  ⊗ const (μ natDesc tt tt)
  ⊗ rec (λ γ → tt , top γ)
  ⊗ ι (λ γ → tt , natDesc-suc (top γ))
  ⊕ `0

test-nat→vec : ornToDesc nat→vec₂ ≡ vecDesc₂
test-nat→vec = refl

--------------------
-- Discussion

data Foo (n : Nat) : Fin n → Set where
  foo : (k : Fin n) → (b : Bool) → Foo n k

{-
fooDesc : DatDesc (ε ▷ (λ γ → Fin {!!})) (ε ▷′ Nat) 1
fooDesc = {!!}
-}

module L where
  postulate
    remember : ∀{I R Γ #c}(D : DatDesc I Γ #c) →
      (α : ∀{γ} → Alg D γ R) →
      ∀{γ i} → (x : μ D γ i) → μ (ornToDesc (algOrn D α)) γ (i , (fold α x))
    recomputation : ∀{I R Γ #c}(D : DatDesc I Γ #c) →
      (α : {γ : ⟦ Γ ⟧} → Alg D γ R) →
      ∀{γ j} → (x : μ (ornToDesc (algOrn D α)) γ j) →
      fold α (forget (algOrn D α) x) ≡ top j

  vecDesc′ : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
  vecDesc′ = ornToDesc (algOrn listDesc lengthAlg)

  length′ : ∀{A} → μ listDesc (tt , A) tt → Nat
  length′ = fold lengthAlg

  vec-to-list : ∀{A n} → μ vecDesc′ (tt , A) (tt , n) →
    μ listDesc (tt , A) tt
  vec-to-list = forget (algOrn listDesc lengthAlg)

  list-to-vec : ∀{A} → (x : μ listDesc (tt , A) tt) →
    μ vecDesc′ (tt , A) (tt , length′ x)
  list-to-vec = remember listDesc lengthAlg

  length-recomputation : ∀{A n} → (x : μ vecDesc′ (tt , A) (tt , n)) →
    length′ (vec-to-list x) ≡ n
  length-recomputation x = recomputation listDesc lengthAlg x


--------------------
-- SEE HERE --> Thesis/SeparateContexts.agda
--------------------


{-
--------------------
-- Example: specialising logins with parameters and give-K

postulate
  Uri Name Password : Set

loginDesc : DatDesc ε ε 1
loginDesc = const Uri ⊗ const Name ⊗ const Password ⊗ ι (λ γ → tt) ⊕ `0

getUri : μ loginDesc tt tt → Uri
getUri ⟨ zero , u , _ ⟩ = u
getUri ⟨ suc () , _ ⟩

postulate
  getLoginInfo : (u : Uri) → Σ (μ loginDesc tt tt) (λ li → getUri li ≡ u)

uriLoginDesc : DatDesc ε (ε ▷′ Uri) 1
uriLoginDesc = const Name ⊗ const Password ⊗ ι (λ γ → tt) ⊕ `0
login→uriLogin : DefOrn ε id (ε ▷′ Uri) (λ i → tt) loginDesc
login→uriLogin = (give-K (λ δ → top δ) $ -⊗ -⊗ ι (λ δ → inv tt)) ⊕ `0

uriLoginToLogin : ∀{u} → μ uriLoginDesc (tt , u) tt → μ loginDesc tt tt
uriLoginToLogin = forget login→uriLogin

postulate
  getLoginInfo′ : (u : Uri) → μ uriLoginDesc (tt , u) tt

module UriLoginInfoIsRefinement (u : Uri) where
  to : Σ (μ loginDesc tt tt) (λ li → getUri li ≡ u) →
       μ uriLoginDesc (tt , u) tt
  to (⟨ zero , _ , y ⟩ , _) = ⟨ 0 , y ⟩
  to (⟨ suc () , _ ⟩ , _)
  from : μ uriLoginDesc (tt , u) tt →
         Σ (μ loginDesc tt tt) (λ li → getUri li ≡ u)
  from ⟨ zero , y ⟩ = ⟨ 0 , u , y ⟩ , refl
  from ⟨ suc () , _ ⟩
  to-from : ∀ x → to (from x) ≡ x
  to-from ⟨ zero , _ ⟩ = refl
  to-from ⟨ suc () , _ ⟩
  from-to : ∀ x → from (to x) ≡ x
  from-to (⟨ zero , _ , _ ⟩ , eq) rewrite eq = refl
  from-to (⟨ suc () , _ ⟩ , _)

  iso : Iso (Σ (μ loginDesc tt tt) (λ li → getUri li ≡ u)) (μ uriLoginDesc (tt , u) tt)
  iso = record { to = to ; from = from ; to-from = to-from ; from-to = from-to }



Bounded trees in the style of mcbride14

data BoundedTree : Nat → Nat → Set where
  leaf : ∀{min max} → BoundedTree min max
  node : ∀{min max} → (x : Nat) → {{low : IsTrue (min ≤? x)}} → {{high : IsTrue (x ≤? max)}} →
         BoundedTree min x → BoundedTree x max → BoundedTree min max

boundedTree-ex : BoundedTree 2 8
boundedTree-ex = node 3 (node 2 leaf leaf) (node 6 leaf leaf)

boundedTreeDesc : DatDesc 2
boundedTreeDesc = const Nat ⊗ const Nat ⊗ ι
 ⊕ {!!}
 ⊕ `0

-}
