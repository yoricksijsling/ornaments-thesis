
{-# OPTIONS --type-in-type #-}

module Thesis.DiscussionTermLang where

open import Common

open import Thesis.SimplifiedContexts

data _∋Set : (Γ : Cx) → Set₁ where
  top′ : ∀{Γ} → (Γ ▷′ Set) ∋Set
  pop′ : ∀{Γ S} → Γ ∋Set → (Γ ▷ S) ∋Set

⟦_⟧∋Set : ∀{Γ} → Γ ∋Set → (γ : ⟦ Γ ⟧) → Set
⟦ top′ ⟧∋Set (γ , t) = t
⟦ pop′ i ⟧∋Set (γ , s) = ⟦ i ⟧∋Set γ

{-
-- The full embedding is a lot more fun, but ultimately not necessary.

data _∋_ : (Γ : Cx) (T : ⟦ Γ ⟧ → Set) → Set₁ where
  top′ : ∀{Γ T} → (Γ ▷ T) ∋ (T ∘ pop)
  pop′ : ∀{Γ S T} → Γ ∋ T → (Γ ▷ S) ∋ (T ∘ pop)
⟦_⟧∋ : ∀{Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧) → T γ
⟦ top′ ⟧∋ (γ , t) = t
⟦ pop′ i ⟧∋ (γ , s) = ⟦ i ⟧∋ γ

mutual
  data _⋆_ (Γ : Cx) : (⟦ Γ ⟧ → Set) → Set₁ where
    `Nat : Γ ⋆ const Nat
    `Set : Γ ⋆ const Set
    `TypeVar : (i : Γ ∋Set) → Γ ⋆ ⟦ i ⟧∋Set
    `Lit : (T : ⟦ Γ ⟧ → Set) → Γ ⋆ T
    `Fin : (n : Γ ⊢ `Nat) → Γ ⋆ (Fin ∘ ⟦ n ⟧⊢)
    `Term : (x : Γ ⊢ `Set) → Γ ⋆ ⟦ x ⟧⊢
    `Var : ∀{T} → Γ ∋ T → Γ ⋆ T
    `Either : ∀{A B} → Γ ⋆ A → Γ ⋆ B → Γ ⋆ (λ γ → Either (A γ) (B γ))
  data _⊢_ (Γ : Cx) : ∀{T} → (Γ ⋆ T) → Set₁ where
    `zero : Γ ⊢ `Nat
    `suc : Γ ⊢ `Nat → Γ ⊢ `Nat
    `lit : ∀{T} → ((γ : ⟦ Γ ⟧) → T γ) → Γ ⊢ `Lit T
    `var : ∀{T} → (i : Γ ∋ T) → Γ ⊢ `Var i
    `varSet : (i : Γ ∋Set) → Γ ⊢ `Set
    `left : ∀{A B}{`A : Γ ⋆ A}{`B : Γ ⋆ B} → Γ ⊢ `A → Γ ⊢ `Either `A `B
    `right : ∀{A B}{`A : Γ ⋆ A}{`B : Γ ⋆ B} → Γ ⊢ `B → Γ ⊢ `Either `A `B
  ⟦_⟧⊢ : ∀{Γ T}{Ty : Γ ⋆ T} → Γ ⊢ Ty → (γ : ⟦ Γ ⟧) → T γ
  ⟦ `zero ⟧⊢ γ = zero
  ⟦ `suc n ⟧⊢ γ = suc (⟦ n ⟧⊢ γ)
  ⟦ `lit v ⟧⊢ γ = v γ
  ⟦ `var i ⟧⊢ γ = ⟦ i ⟧∋ γ
  ⟦ `varSet i ⟧⊢ γ = ⟦ i ⟧∋Set γ
  ⟦ `left x ⟧⊢ γ = left (⟦ x ⟧⊢ γ)
  ⟦ `right x ⟧⊢ γ = right (⟦ x ⟧⊢ γ)

`Nat-example : ε ⊢ `Nat 
`Nat-example = `suc `zero

interpret-`Nat-example : Nat
interpret-`Nat-example = ⟦ `Nat-example ⟧⊢ tt
-}

infixr 3 _⊕_
infixr 4 _⊗_
data Desc (Γ : Cx) : Set₁ where
  ι : Desc Γ
  rec : Desc Γ
  -- val : ∀{S} (p : Γ ⋆ S) → Desc Γ
  par : (i : Γ ∋Set) → Desc Γ
  _⊕_ : Desc Γ → Desc Γ → Desc Γ
  _⊗_ : Desc Γ → Desc Γ → Desc Γ

⟦_⟧desc : ∀{Γ} → Desc Γ → ⟦ Γ ⟧Cx → Set → Set
⟦ ι ⟧desc γ X = ⊤
⟦ rec ⟧desc γ X = X
-- ⟦ val {S = S} x ⟧desc γ X = S γ
⟦ par i ⟧desc γ X = ⟦ i ⟧∋Set γ
⟦ A ⊕ B ⟧desc γ X = Either (⟦ A ⟧desc γ X) (⟦ B ⟧desc γ X)
⟦ A ⊗ B ⟧desc γ X = ⟦ A ⟧desc γ X × ⟦ B ⟧desc γ X

data μ {Γ}(D : Desc Γ) (γ : ⟦ Γ ⟧) : Set where
  ⟨_⟩ : ⟦ D ⟧desc γ (μ D γ) → μ D γ

data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

treeDesc : Desc (ε ▷′ Set)
treeDesc = par top′ ⊕ rec ⊗ rec

tree-to : ∀{A} → Tree A → μ treeDesc (tt , A)
tree-to (leaf v) = ⟨ left v ⟩
tree-to (node xs ys) = ⟨ right (tree-to xs , tree-to ys) ⟩

descmap : ∀{Γ X Y} (f : X → Y) (D : Desc Γ) →
  ∀{γ} → (v : ⟦ D ⟧desc γ X) → ⟦ D ⟧desc γ Y
descmap f ι tt = tt
descmap f rec v = f v
descmap f (par i) v = v
descmap f (A ⊕ B) (left x) = left (descmap f A x)
descmap f (A ⊕ B) (right x) = right (descmap f B x)
descmap f (A ⊗ B) (x , y) = descmap f A x , descmap f B y

Alg : ∀{Γ} → Desc Γ → ⟦ Γ ⟧ → Set → Set
Alg D γ X = ⟦ D ⟧desc γ X → X

module _ {Γ}{D : Desc Γ}{γ X} (α : Alg D γ X) where
  {-# TERMINATING #-}
  fold : μ D γ → X
  fold ⟨ xs ⟩ = α (descmap fold D xs)

flattenAlg : ∀{Γ} (D : Desc (Γ ▷′ Set)) →
  ∀{γ A} → Alg D (γ , A) (List A)
flattenAlg ι tt = []
flattenAlg rec x = x
flattenAlg (par top′) x = [ x ]
flattenAlg (par _) x = []
flattenAlg (A ⊕ B) (left x) = flattenAlg A x
flattenAlg (A ⊕ B) (right x) = flattenAlg B x
flattenAlg (A ⊗ B) (x , y) = flattenAlg A x ++ flattenAlg B y

flatten : ∀{Γ} (D : Desc (Γ ▷′ Set)) →
  ∀{γ A} → μ D (γ , A) → List A
flatten D = fold (flattenAlg D)

pmapNT : ∀{Γ} (D : Desc (Γ ▷′ Set)) →
  ∀{γ A B X} → (f : A → B) → ⟦ D ⟧desc (γ , A) X → ⟦ D ⟧desc (γ , B) X
pmapNT ι f tt = tt
pmapNT rec f v = v
pmapNT (par top′) f v = f v
pmapNT (par (pop′ i)) f v = v
pmapNT (A ⊕ B) f (left x) = left (pmapNT A f x)
pmapNT (A ⊕ B) f (right x) = right (pmapNT B f x)
pmapNT (A ⊗ B) f (x , y) = pmapNT A f x , pmapNT B f y

{-# TERMINATING #-}
pmap : ∀{Γ} (D : Desc (Γ ▷′ Set)) →
  ∀{γ A B} → (f : A → B) → μ D (γ , A) → μ D (γ , B)
pmap D {γ} {A} f ⟨ x ⟩ = ⟨ (pmapNT D f (descmap (pmap D f) D x)) ⟩

tree-example : Tree Nat
tree-example = node (leaf 7) (node (node (leaf 5) (leaf 3)) (leaf 1))
test-flatten : fold (flattenAlg treeDesc) (tree-to tree-example)
  ≡ 7 ∷ 5 ∷ 3 ∷ 1 ∷ []
test-flatten = refl

tree-example-double : Tree Nat
tree-example-double = node (leaf 14) (node (node (leaf 10) (leaf 6)) (leaf 2))

test-pmap : pmap treeDesc (_*_ 2) (tree-to tree-example)
  ≡ tree-to tree-example-double
test-pmap = refl
