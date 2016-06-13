module Common where

open import Prelude hiding ( _***_; _***′_; first; second
                           ; uncurry; uncurry′
                           ; getArgs
                           ; insert ) public
open import HeterogeneousEquality public

Extensionality : (a b : Level) → Set _
Extensionality a b =
  {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) → f ≡ g

--------------------
-- Some combinators

-- S combinator, is also <*> of applicative functor
infixl 4 _<S>_
_<S>_ : ∀ {a b c} {Γ : Set a} {S : Γ → Set b} {T : (γ : Γ) → S γ → Set c} →
  (f : (γ : Γ) (s : S γ) → T γ s) → (s : (γ : Γ) → S γ) →
  (γ : Γ) → T γ (s γ)
f <S> s = λ γ → f γ (s γ)

-- S combined with K gives <$>, which is actually just function composition
infixl 4 _<KS>_
_<KS>_ : ∀ {a b c} {Γ : Set a} {S : Set b} {T : S → Set c} →
  (f : (s : S) → T s) → (s : (γ : Γ) → S) →
  (γ : Γ) → T (s γ)
f <KS> s = const f <S> s

--------------------
-- Overwriting the implementations of some functions on products

map× _***_ : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
       (f : A₁ → A₂) → (∀ {x} → B₁ x → B₂ (f x)) → Σ A₁ B₁ → Σ A₂ B₂
map× f g p = f (fst p) , g (snd p)
_***_ f g p = f (fst p) , g (snd p)

uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} →
            (∀ x (y : B x) → C x y) → (p : Σ A B) → C (fst p) (snd p)
uncurry f p = f (fst p) (snd p)

uncurry′ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c} →
            (∀ x → B x → C) → Σ A B → C
uncurry′ = uncurry

first : ∀ {a₁ a₂ b} {A₁ : Set a₁} {A₂ : Set a₂} {B : Set b} →
          (A₁ → A₂) → A₁ × B → A₂ × B
first f = map× f id

second : ∀ {a b₁ b₂} {A : Set a} {B₁ : A → Set b₁} {B₂ : A → Set b₂} →
           (∀ {x} → B₁ x → B₂ x) → Σ A B₁ → Σ A B₂
second f = map× id f

private
  module Test where
    -- In Prelude the pair is defined as a datatype, where it was a record in stdlib.
    -- Now because functions like _***_ and uncurry do a pattern match they give some problems when we want to prove stuff.
    -- For instance the following:

    f : (⊤ × List Nat) → List Nat
    -- f (tt , y) = y
    f p = snd p

    g : List Nat → ⊤ × List Nat
    g [] = tt , []
    g (x ∷ xs) = map× id (_∷_ x) (g xs)
    -- g (x ∷ xs) = _***_ id (_∷_ x) (g xs)

    fg : ∀ xs → f (g xs) ≡ xs
    fg [] = refl
    fg (x ∷ xs) = cong (_∷_ x) (fg xs) -- This does not work if we pattern match on the pair somewhere in f or g.

record Iso {ℓ : Level}(A B : Set ℓ) : Set ℓ where
  field
    to : A → B
    from : B → A
    to-from : ∀ x → to (from x) ≡ x
    from-to : ∀ x → from (to x) ≡ x

record Semantics {α β : Level}(A : Set α) : Set (α ⊔ lsuc β) where
  field
    {⟦⟧-Type} : Set β
    ⟦_⟧ : A → ⟦⟧-Type
open Semantics {{...}} public

_→ⁱ_ : {I : Set} → (I → Set) → (I → Set) → Set
X →ⁱ Y = ∀{i} → X i → Y i


------------------------------
-- Inverses

module _ {a b}{A : Set a}{B : Set b} where
  -- |f ⁻¹ y| contains an |x| such that |f x ≡ y|
  data _⁻¹_ (f : A → B) : (y : B) → Set (a ⊔ b) where
    inv : (x : A) → f ⁻¹ (f x)

  uninv : {f : A → B}{y : B} → f ⁻¹ y → A
  uninv (inv x) = x

  inv-eq : {f : A → B}{y : B} → (x : f ⁻¹ y) → f (uninv x) ≡ y
  inv-eq (inv x) = refl

module InverseImageAlt {a b}{A : Set a}{B : Set b} where
  -- Alternative representation of |_⁻¹_|
  AltInv : (f : A → B) (y : B) → Set (a ⊔ b)
  AltInv f y = Σ A λ x → f x ≡ y

  to : (f : A → B) (y : B) → f ⁻¹ y → AltInv f y
  to f .(f x) (inv x) = x , refl
  from : (f : A → B) (y : B) → AltInv f y → f ⁻¹ y
  from f .(f x) (x , refl) = inv x
  to-from : (f : A → B) (y : B) → ∀ i → to f y (from f y i) ≡ i
  to-from f .(f x) (x , refl) = refl
  from-to : (f : A → B) (y : B) → ∀ i → from f y (to f y i) ≡ i
  from-to f .(f x) (inv x) = refl

  AltInv-iso : (f : A → B) (y : B) → Iso (f ⁻¹ y) (AltInv f y)
  AltInv-iso f y = record { to = to f y ; from = from f y
                          ; to-from = to-from f y ; from-to = from-to f y
                          }

inv-∘ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}{f : B → C}{g : A → B}
        {z : C} → (y : f ⁻¹ z) → (x : g ⁻¹ uninv y) → (f ∘ g) ⁻¹ z
inv-∘ (inv _) (inv x) = inv x

uninv-inv-∘ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}{f : B → C}{g : A → B}
              {z : C} → (y : f ⁻¹ z) → (x : g ⁻¹ uninv y) →
              uninv (inv-∘ y x) ≡ uninv x
uninv-inv-∘ (inv _) (inv x) = refl
