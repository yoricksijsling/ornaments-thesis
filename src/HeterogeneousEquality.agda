module HeterogeneousEquality where

infix 4 _≅_
data _≅_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set ℓ where
   refl : x ≅ x

≅-cong : ∀ {a b} {A : Set a} {B : A → Set b} {x y}
         (f : (x : A) → B x) → x ≅ y → f x ≅ f y
≅-cong f refl = refl

≅-cong₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          {x y u v}
        (f : (x : A) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
≅-cong₂ f refl refl = refl
