
module Thesis.Sop where

open import Common

-- Introduction is on the bottom of this page


module PatternFunctors where

  -- PF atoms : ⊤, ×, Either

  boolLike : Set
  boolLike = Either ⊤ ⊤

  -- pairOfNats : Set
  -- pairOfNats = Nat × Nat

  maybeLike : (A : Set) → Set
  maybeLike A = Either A ⊤

  {-# NON_TERMINATING #-}
  listLike : (A : Set) → Set
  listLike A = Either ⊤ (listLike A)

  natPF : Set → Set
  natPF X = Either ⊤ X

  listPF : (A : Set) → Set → Set
  listPF A X = Either ⊤ (A × X)

  -- binaryTreePF : (A : Set) → Set → Set
  -- binaryTreePF A X = Either ⊤ (A × X × X)

  {-# NO_POSITIVITY_CHECK #-}
  data μ′ (F : Set → Set) : Set where
    ⟨_⟩ : F (μ′ F) → μ′ F

  -- nat3 : μ′ natPF
  -- nat3 = ⟨ right ⟨ right ⟨ left tt ⟩ ⟩ ⟩

  listPF-example : μ′ (listPF String)
  listPF-example = ⟨ right ("one" , ⟨ right ("two" , ⟨ left tt ⟩) ⟩) ⟩

  -- {-# NO_POSITIVITY_CHECK #-}
  -- data μⁱ {I : Set} (F : (I → Set) → (I → Set)) : I → Set where
  --   ⟨_⟩ : ∀{i} → F (μⁱ F) i → μⁱ F i

  -- vecPF : (A : Set) → (Nat → Set) → (Nat → Set)
  -- vecPF A X o = Either (o ≡ 0) (Σ Nat λ n → A × X n × (o ≡ suc n))

  -- vecEx : μⁱ (vecPF String) 1
  -- vecEx = ⟨ 1 , _ , "one" , ⟨ 0 , refl ⟩ , refl ⟩


----------------------------------------
-- Descriptions

infixr 3 _⊕_
infixr 4 _⊗_ rec-⊗_

data ConDesc : Set₁ where
  ι : ConDesc
  _⊗_ : (S : Set) → (xs : ConDesc) → ConDesc
  rec-⊗_ : (xs : ConDesc) → ConDesc
data DatDesc : Nat → Set₁ where
  `0 : DatDesc 0
  _⊕_ : ∀{#c} (x : ConDesc) (xs : DatDesc #c) → DatDesc (suc #c)

⟦_⟧conDesc : ConDesc → Set → Set
⟦ ι ⟧conDesc X = ⊤
⟦ S ⊗ D ⟧conDesc X = S × ⟦ D ⟧conDesc X
⟦ rec-⊗ D ⟧conDesc X = X × ⟦ D ⟧conDesc X

lookupCtor : ∀{#c}(D : DatDesc #c) → Fin #c → ConDesc
lookupCtor `0 ()
lookupCtor (x ⊕ _) zero = x
lookupCtor (_ ⊕ xs) (suc k) = lookupCtor xs k

⟦_⟧datDesc : ∀{#c} → DatDesc #c → Set → Set
⟦_⟧datDesc {#c} D X = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc X

instance conDesc-semantics : Semantics ConDesc
         conDesc-semantics = record { ⟦_⟧ = ⟦_⟧conDesc }
         datDesc-semantics : ∀{#c} → Semantics (DatDesc #c)
         datDesc-semantics = record { ⟦_⟧ = ⟦_⟧datDesc }
{-# DISPLAY ⟦_⟧conDesc x = ⟦_⟧ x #-}
{-# DISPLAY ⟦_⟧datDesc x = ⟦_⟧ x #-}

-- |⟦_⟧| can mean either |⟦_⟧conDesc| or |⟦_⟧datDesc|
data μ {#c : Nat}(F : DatDesc #c) : Set where
  ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F


----------------------------------------
-- Map

conDescmap : ∀{X Y} (f : X → Y) (D : ConDesc) →
             (v : ⟦ D ⟧ X) → ⟦ D ⟧ Y
conDescmap f ι tt = tt
conDescmap f (S ⊗ xs) (s , v) = s , conDescmap f xs v
conDescmap f (rec-⊗ xs) (s , v) = f s , conDescmap f xs v

datDescmap : ∀{#c X Y} (f : X → Y) (D : DatDesc #c) →
             (v : ⟦ D ⟧ X) → ⟦ D ⟧ Y
datDescmap f xs (k , v) = k , conDescmap f (lookupCtor xs k) v


----------------------------------------
-- Folding

DatAlg : ∀{#c} → DatDesc #c → Set → Set
DatAlg D X = ⟦ D ⟧ X → X

{-# TERMINATING #-}
fold : ∀{#c}{D : DatDesc #c}{X} (α : DatAlg D X) → μ D → X
fold {D = D} α ⟨ xs ⟩ = α (datDescmap (fold α) D xs)


--------------------------------------------------
-- Ornaments

infixr 4 -⊗_ _+⊗_ rec-+⊗_
data ConOrn : (D : ConDesc) → Set₁ where
  ι : ConOrn ι
  -⊗_ : ∀{S xs} → (xs⁺ : ConOrn xs) → ConOrn (S ⊗ xs)
  rec-⊗_ : ∀{xs} → (xs⁺ : ConOrn xs) → ConOrn (rec-⊗ xs)

  _+⊗_ : ∀{xs}(S : Set) → (xs⁺ : ConOrn xs) → ConOrn xs
  rec-+⊗_ : ∀{xs} → (xs⁺ : ConOrn xs) → ConOrn xs

  give-K : ∀{S xs} (s : S) → (xs⁺ : ConOrn xs) → ConOrn (S ⊗ xs)
  -- give-rec : ∀{xs} → ? → (xs⁺ : ConOrn xs) → ConOrn (rec-⊗ xs)

data DatOrn : ∀{#c}(D : DatDesc #c) → Set₁ where
  `0 : DatOrn `0
  _⊕_ : ∀{#c x xs} →
        (x⁺ : ConOrn x) (xs⁺ : DatOrn xs) → DatOrn {suc #c} (x ⊕ xs)

{-
  recons :
    ∀ #c⁺ {#c} {D : DatDesc #c} →
    (f : (k⁺ : Fin #c⁺) → (Σ (Fin #c) λ k → ConOrn (lookupCtor D k))) →
    DatOrn {#c} D
-}

conOrnToDesc : ∀{D} → ConOrn D → ConDesc
conOrnToDesc ι = ι
conOrnToDesc (-⊗_ {S = S} xs⁺) = S ⊗ conOrnToDesc xs⁺
conOrnToDesc (rec-⊗ xs⁺) = rec-⊗ conOrnToDesc xs⁺
conOrnToDesc (S +⊗ xs⁺) = S ⊗ conOrnToDesc xs⁺
conOrnToDesc (rec-+⊗ xs⁺) = rec-⊗ conOrnToDesc xs⁺
conOrnToDesc (give-K s xs⁺) = conOrnToDesc xs⁺
ornToDesc : ∀{#c}{D : DatDesc #c} → DatOrn D → DatDesc #c
ornToDesc `0 = `0
ornToDesc (x⁺ ⊕ xs⁺) = conOrnToDesc x⁺ ⊕ ornToDesc xs⁺

{-
tabulateCtors : ∀{n} → (Fin n → ConDesc) → DatDesc n
tabulateCtors {zero} f = `0
tabulateCtors {suc n} f = f 0 ⊕ tabulateCtors (f ∘ suc)

ornToDesc-#c : ∀{#c}{D : DatDesc #c} → DatOrn D → Nat
ornToDesc-#c `0 = 0
ornToDesc-#c (_ ⊕ xs⁺) = suc (ornToDesc-#c xs⁺)
ornToDesc-#c (recons n _) = n

ornToDesc : ∀{#c}{D : DatDesc #c} →
  (o : DatOrn D) → DatDesc (ornToDesc-#c o)
ornToDesc `0 = `0
ornToDesc (x⁺ ⊕ xs⁺) = conOrnToDesc x⁺ ⊕ ornToDesc xs⁺
ornToDesc (recons _ xs⁺) = tabulateCtors (conOrnToDesc ∘ snd ∘ xs⁺)
-}

----------------------------------------
-- Ornamental Algebra

conForgetNT : ∀{D} (o : ConOrn D) →
              ∀{X} → ⟦ conOrnToDesc o ⟧ X → ⟦ D ⟧ X
conForgetNT ι tt = tt
conForgetNT (-⊗ xs⁺) (s , v) = s , conForgetNT xs⁺ v
conForgetNT (rec-⊗ xs⁺) (s , v) = s , conForgetNT xs⁺ v
conForgetNT (_+⊗_ S xs⁺) (s , v) = conForgetNT xs⁺ v
conForgetNT (rec-+⊗_ xs⁺) (s , v) = conForgetNT xs⁺ v
conForgetNT (give-K s xs⁺) v = s , conForgetNT xs⁺ v

forgetNT : ∀{#c}{D : DatDesc #c} (o : DatOrn D) →
           ∀{X} → ⟦ ornToDesc o ⟧ X → ⟦ D ⟧ X
forgetNT `0 (() , _)
forgetNT (x⁺ ⊕ xs⁺) (zero , v) = 0 , conForgetNT x⁺ v
forgetNT (x⁺ ⊕ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

{-
lookup-tabulate : ∀{#c}(f : Fin #c → ConDesc) i →
                  lookupCtor (tabulateCtors f) i ≡ f i
lookup-tabulate f zero = refl
lookup-tabulate f (suc i) = lookup-tabulate (f ∘ suc) i

forgetNT : ∀{#c}{D : DatDesc #c} (o : DatOrn D) →
           ∀{X} → ⟦ ornToDesc o ⟧ X → ⟦ D ⟧ X
forgetNT `0 (() , _)
forgetNT (x⁺ ⊕ xs⁺) (zero , v) = 0 , conForgetNT x⁺ v
forgetNT (x⁺ ⊕ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))
forgetNT (recons _ f) {X} (c , v) =
  let v′ = transport (λ a → ⟦_⟧ a X) (lookup-tabulate _ c) v in
  fst (f c) , conForgetNT (snd (f c)) v′
-}

forgetAlg : ∀{#c}{D : DatDesc #c} (o : DatOrn D) →
            DatAlg (ornToDesc o) (μ D)
forgetAlg o = ⟨_⟩ ∘ forgetNT o

forget : ∀{#c}{D : DatDesc #c} (o : DatOrn D) →
         μ (ornToDesc o) → μ D
forget o = fold (forgetAlg o)

----------------------------------------

-- Descriptions

unitDesc : DatDesc 1
unitDesc = ι ⊕ `0

natDesc : DatDesc 2
natDesc = ι ⊕ rec-⊗ ι ⊕ `0

pairDesc : (A B : Set) → DatDesc 1
pairDesc A B = A ⊗ B ⊗ ι ⊕ `0

listDesc : (A : Set) → DatDesc 2
listDesc A = ι ⊕ A ⊗ rec-⊗ ι ⊕ `0

{-
nat-example₁ : μ natDesc
nat-example₁ = ⟨ {!!} ⟩
-- Goal: |⟦ natDesc ⟧ (μ natDesc)|
-- Expands to: |Σ (Fin 2) (λ k → ⟦ lookupCtor natDesc k ⟧ (μ natDesc))|

nat-example₂ : μ natDesc
nat-example₂ = ⟨ 1 , {!!} ⟩
-- Goal: |⟦ lookupCtor natDesc 1 ⟧ (μ natDesc)|
-- Expands to: |⟦ rec-⊗ ι ⟧ (μ natDesc)|
-- Expands to: |μ natDesc × ⊤|

nat-example₃ : μ natDesc
nat-example₃ = ⟨ 1 , ⟨ 0 , tt ⟩ , tt ⟩
-}

`zero : μ natDesc
`zero = ⟨ 0 , tt ⟩
`suc : μ natDesc → μ natDesc
`suc n = ⟨ 1 , n , tt ⟩

infixr 5 _`∷_
`[] : ∀{A} → μ (listDesc A)
`[] = ⟨ 0 , tt ⟩
_`∷_ : ∀{A} → A → μ (listDesc A) → μ (listDesc A)
_`∷_ x xs = ⟨ 1 , x , xs , tt ⟩

nat-example : `suc `zero ≡ ⟨ 1 , ⟨ 0 , tt ⟩ , tt ⟩
nat-example = refl
-- list-example : 7 `∷ 8 `∷ `[] ≡ ⟨ 1 , 7 , ⟨ 1 , 8 , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩
list-example : _≡_ {A = μ (listDesc Nat)} (7 `∷ 8 `∷ `[]) ⟨ 1 , 7 , ⟨ 1 , 8 , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩
list-example = refl

module ListIso (A : Set) where
  postulate
    to : List A → μ (listDesc A)
    from : μ (listDesc A) → List A
    to-from : ∀ x → from (to x) ≡ x
    from-to : ∀ x → to (from x) ≡ x


-- Maps/folds

sumAlg : DatAlg (listDesc Nat) Nat
sumAlg (zero , tt) = 0
sumAlg (suc zero , x , xs , tt) = x + xs
sumAlg (suc (suc ()) , _)

countTruesAlg : DatAlg (listDesc Bool) Nat
countTruesAlg (zero , tt) = 0
countTruesAlg (suc zero , x , xs , tt) = if x then suc xs else xs
countTruesAlg (suc (suc ()) , _)

countTrues : μ (listDesc Bool) → Nat
countTrues = fold countTruesAlg

-- exprDesc : DatDesc 3
-- exprDesc = Nat ⊗ ι -- lit
--   ⊕ rec-⊗ rec-⊗ ι -- +
--   ⊕ rec-⊗ rec-⊗ ι -- *
--   ⊕ `0

-- exprEvalAlg : DatAlg exprDesc Nat
-- exprEvalAlg (zero , n , tt) = n
-- exprEvalAlg (suc zero , x , y , tt) = x + y
-- exprEvalAlg (suc (suc zero) , x , y , tt) = x * y
-- exprEvalAlg (suc (suc (suc ())) , _)

-- exprEval : μ exprDesc → Nat
-- exprEval = fold exprEvalAlg

-- `lit : Nat → μ exprDesc
-- `lit n = ⟨ 0 , n , tt ⟩

-- test-7*5+8 : exprEval ⟨ 1 , ⟨ 2 , `lit 7 , `lit 5 , tt ⟩ , `lit 8 , tt ⟩ ≡ 43
-- test-7*5+8 = refl



-- Ornaments

listIdOrn : ∀{A} → DatOrn (listDesc A)
listIdOrn = ι ⊕ -⊗ rec-⊗ ι ⊕ `0

nat→list : ∀{A} → DatOrn natDesc
nat→list {A} = ι ⊕ A +⊗ rec-⊗ ι ⊕ `0

test-nat→list : ∀{A} → ornToDesc nat→list ≡ listDesc A
test-nat→list = refl


-- Ornamental algebras

`length : ∀{A} → μ (listDesc A) → μ natDesc
`length = forget nat→list

test-length : `length {A = String} ("one" `∷ "two" `∷ `[]) ≡ `suc (`suc `zero)
-- test-length : `length ("one" `∷ "two" `∷ `[]) ≡ `suc (`suc `zero)
test-length = refl


-- Example: rec-+⊗_

-- list→trees: DatOrn



-- Example: give-K

list→listof7s : DatOrn (listDesc Nat)
list→listof7s = ι ⊕ give-K 7 (rec-⊗ ι) ⊕ `0

test-list→listof7s : ornToDesc list→listof7s ≡ natDesc
test-list→listof7s = refl

forget-listof7s : forget list→listof7s (`suc (`suc `zero)) ≡ (7 `∷ 7 `∷ `[])
forget-listof7s = refl

`replicate : ∀{A} → A → μ natDesc → μ (listDesc A)
`replicate x = forget (ι ⊕ give-K x (rec-⊗ ι) ⊕ `0)

-- _InverseOrnOf_ : ∀{#c}{D : DatDesc #c} → (o₁ : DatOrn D) → (o₂ : DatOrn (ornToDesc o₁)) → Set₁
-- _InverseOrnOf_ {D = D} o₁ o₂ = Σ (ornToDesc o₂ ≡ D) λ eq →
--                                  ∀ x → forget o₁ (forget o₂ x) ≡ transport μ eq x

-- a : nat→list InverseOrnOf list→listof7s
-- a = refl , b
--   where
--   b : (x : μ (ornToDesc list→listof7s)) →
--       forget nat→list (forget list→listof7s x) ≡ transport μ refl x
--   b ⟨ zero , tt ⟩ = refl
--   b ⟨ suc zero , x ,  tt ⟩ rewrite b x = refl
--   b ⟨ suc (suc ()) , _ ⟩


--------------------
-- Discussion

data DescΣ : Set₁ where
  ι : DescΣ
  σ : (S : Set) → (xs : S → DescΣ) → DescΣ
  rec-×_ : (xs : DescΣ) → DescΣ

⟦_⟧DescΣ : DescΣ → Set → Set
⟦ ι ⟧DescΣ X = ⊤
⟦ σ S xs ⟧DescΣ X = Σ S λ s → ⟦ xs s ⟧DescΣ X
⟦ rec-× xs ⟧DescΣ X = X × ⟦ xs ⟧DescΣ X

instance DescΣ-semantics : Semantics DescΣ
         DescΣ-semantics = record { ⟦_⟧ = ⟦_⟧DescΣ }
{-# DISPLAY ⟦_⟧DescΣ x = ⟦_⟧ x #-}

data μΣ (D : DescΣ) : Set where
  ⟨_⟩ : ⟦ D ⟧DescΣ (μΣ D) → μΣ D

emptyDescΣ : DescΣ
emptyDescΣ = σ ⊥ ⊥-elim

pairDescΣ : (A B : Set) → DescΣ
pairDescΣ A B = σ A λ a → σ B λ b → ι

eitherDescΣ : (A B : Set) → DescΣ
eitherDescΣ A B = σ (Fin 2) λ
  { zero → σ A λ a → ι
  ; (suc zero) → σ B λ b → ι
  ; (suc (suc ())) }

eitherDescΣ-left : ∀{A B} → A → μΣ (eitherDescΣ A B)
eitherDescΣ-left x = ⟨ 0 , x , tt ⟩
eitherDescΣ-right : ∀{A B} → B → μΣ (eitherDescΣ A B)
eitherDescΣ-right x = ⟨ 1 , x , tt ⟩

data OrnΣ : (D : DescΣ) → Set₁ where
  ι : OrnΣ ι
  σ : (S : Set) → ∀{xs} (xs⁺ : (s : S) → OrnΣ (xs s)) → OrnΣ (σ S xs)
  rec-×_ : ∀{xs} (xs⁺ : OrnΣ xs) → OrnΣ (rec-× xs)
  insert-σ : (S : Set) → ∀{xs} → (xs⁺ : S → OrnΣ xs) → OrnΣ xs
  delete-σ : ∀{S xs} → (s : S) → (xs⁺ : OrnΣ (xs s)) → OrnΣ (σ S xs)

ornToDescΣ : ∀{D} → OrnΣ D → DescΣ
ornToDescΣ ι = ι
ornToDescΣ (σ S xs⁺) = σ S (λ s → ornToDescΣ (xs⁺ s))
ornToDescΣ (rec-× xs⁺) = rec-× (ornToDescΣ xs⁺)
ornToDescΣ (insert-σ S xs⁺) = σ S (λ s → ornToDescΣ (xs⁺ s))
ornToDescΣ (delete-σ s xs⁺) = ornToDescΣ xs⁺

natDescΣ : DescΣ
natDescΣ = σ (Fin 2) λ
  { zero → ι
  ; (suc zero) → rec-× ι
  ; (suc (suc ())) }

-- listDescΣ : (A : Set) → DescΣ
-- listDescΣ A = σ (Fin 2) λ
--   { zero → ι
--   ; (suc zero) → σ A λ a → rec-× ι
--   ; (suc (suc ())) }

nat→listΣ : (A : Set) → OrnΣ natDescΣ
nat→listΣ A = σ (Fin 2) λ
  { zero → ι
  ; (suc zero) → insert-σ A λ a → rec-× ι
  ; (suc (suc ())) }
-- test-nat→listΣ : (ext : ∀{a b} → Extensionality a b) → ∀{A} → ornToDescΣ (nat→listΣ A) ≡ listDescΣ A
-- test-nat→listΣ ext {A} = cong (σ (Fin 2)) $ ext λ { zero → refl
--                                                    ; (suc zero) → refl
--                                                    ; (suc (suc ())) }

boolsDescΣ : DescΣ
boolsDescΣ = σ Nat rest
  where rest : Nat → DescΣ
        rest zero = ι
        rest (suc n) = σ Bool λ _ → rest n

boolsDescΣ-example : μΣ boolsDescΣ
boolsDescΣ-example = ⟨ 3 , true , false , true , tt ⟩


-- Relation between ConOrn/DatOrn and OrnΣ

ConOrnSimilar : ∀{D DΣ} → ConOrn D → OrnΣ DΣ → Set₁
ConOrnSimilar {D = D} {DΣ} o oΣ = ⟦ D ⟧ ≡ ⟦ DΣ ⟧ → ⟦ conOrnToDesc o ⟧ ≡ ⟦ ornToDescΣ oΣ ⟧
DatOrnSimilar : ∀{#c}{D : DatDesc #c}{DΣ : DescΣ} → DatOrn D → OrnΣ DΣ → Set₁
DatOrnSimilar {D = D} {DΣ} o oΣ = ⟦ D ⟧ ≡ ⟦ DΣ ⟧ → ⟦ ornToDesc o ⟧ ≡ ⟦ ornToDescΣ oΣ ⟧

-- Swap the constructors of naturals
swapnatΣ : OrnΣ natDescΣ
swapnatΣ = insert-σ (Fin 2) λ
  { zero → delete-σ 1 (rec-× ι)
  ; (suc zero) → delete-σ 0 ι
  ; (suc (suc ())) }

{-
swapnat : DatOrn natDesc
swapnat = recons 2 λ
  { zero → 1 , rec-⊗ ι
  ; (suc zero) → 0 , ι
  ; (suc (suc ())) }
-}
