module ContextFree.Multi.Desc.Core where

open import Common
open import Builtin.Size

ISet : Set → Set₁
ISet I = I → Set

-- Index-preserving functions
_→↑_ : ∀ {I} → (r s : ISet I) → Set
r →↑ s = ∀ i → r i → s i

infixr 5 _∣_
_∣_  : {I J : Set} → ISet I → ISet J → (Either I J) → Set
_∣_ r s (left i) = r i
_∣_ r s (right j) = s j

map∣ : {I J : Set}{r r′ : ISet I}{s s′ : ISet J} →
             r →↑ r′ → s →↑ s′ →
             (r ∣ s) →↑ (r′ ∣ s′)
map∣ f g (left i) r = f i r
map∣ f g (right j) s = g j s

-- Heterogeneous predicate transformer
IOFunc : Set → Set → Set₁
IOFunc I O = ISet I → ISet O

infixr 3 _`+_
infixr 4 _`*_

mutual
  data IODesc : Set → Set → Set₁ where
    `0 : ∀{I O} → IODesc I O
    `1 : ∀{I O} → IODesc I O
    _`+_ : ∀{I O} → (A B : IODesc I O) → IODesc I O
    _`*_ : ∀{I O} → (A B : IODesc I O) → IODesc I O
    `var : ∀{I O} → (i : I) → IODesc I O
    `! : ∀{I O} → (o′ : O) → IODesc I O
    -- `Σ : ∀{I O} → {C : IODesc ⊥ ⊤} →
    --      (p : ⟦ C ⟧ ⊥-elim tt → IODesc I O) → IODesc I O
    -- `iso : ∀{O} → (C : IODesc ⊥ O) → (D : IOFunc ⊥ O) → IODesc ⊥ O
           -- ((r : ISet I) → (o : O) → D r o ≡ ⟦ C ⟧ r o) → IODesc I O
    `fix : ∀{I O} → (C : IODesc (Either I O) O) → IODesc I O

    -- Or should the index be ⊤??

  ⟦_⟧ : ∀{I O} → IODesc I O → {s : Size} → IOFunc I O
  ⟦_⟧ `0 r o = ⊥
  ⟦_⟧ `1 r o = ⊤
  ⟦_⟧ (A `+ B) r o = Either (⟦ A ⟧ r o) (⟦ B ⟧ r o)
  ⟦_⟧ (A `* B) r o = ⟦ A ⟧ r o × ⟦ B ⟧ r o
  ⟦_⟧ (`var i) r o = r i
  ⟦_⟧ (`! o′) r o = o ≡ o′
  -- ⟦_⟧ (`Σ p) r o = Σ _ (λ i → ⟦ p i ⟧ r o)
  -- ⟦_⟧ (`iso _ D) _ o = D ⊥-elim o
  ⟦_⟧ (`fix F) {sz} r o = μ F r o {sz}

  -- The use of sizes here seems to be somewhat similar to that of Conor McBride in Turing-completeness totally free
  data μ {I O : Set} (F : IODesc (Either I O) O)
         (r : ISet I) (o : O) : {sz : Size} → Set where
    ⟨_⟩ : {sz : Size} → ⟦ F ⟧ {sz} (r ∣ ⟦ `fix F ⟧ {sz} r) o → μ F r o {↑ sz}

-- normal map: (x → y) → (F x → F y)
-- map on indexed: (x →↑ y) → (F x →↑ F y)

-- 1. fmap id = id
-- 2. fmap (f ∘ g) = fmap f ∘ fmap g
  
desc-map : ∀ {I O}{r s : ISet I} → (D : IODesc I O) → r →↑ s → {sz : Size} → ⟦ D ⟧ {sz} r →↑ ⟦ D ⟧ {sz} s
desc-map `0 f o = id
desc-map `1 f o = id
desc-map (A `+ B) f o = mapEither (desc-map A f o) (desc-map B f o)
desc-map (A `* B) f o = map× (desc-map A f o) (desc-map B f o)
desc-map (`var i) f o = f i
desc-map (`! o′) f o = id
-- desc-map (`Σ p) f o = map× id (λ {x} → desc-map (p x) f o)
-- desc-map (`iso C D) f o = id
desc-map (`fix F) f o ⟨ x ⟩ = ⟨ desc-map F (map∣ f (desc-map (`fix F) f)) o x ⟩
