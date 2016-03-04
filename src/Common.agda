module Common where

open import Prelude hiding ( _***_; _***′_; first; second
                           ; uncurry; uncurry′
                           ; getArgs) public



map× : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
       (f : A₁ → A₂) → (∀ {x} → B₁ x → B₂ (f x)) → Σ A₁ B₁ → Σ A₂ B₂
map× f g p = f (fst p) , g (snd p)

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

module _ where
  private
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


