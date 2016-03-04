module ContextFree.Multi.DescEquality where

open import Common
open import ContextFree.Multi.Desc

instance
  ∣fix-cong : ∀ {I O} {F : IODesc (Either I O) O} {r s : ISet I} → {{ rs : r ≡ s }} → r ∣ ⟦ `fix F ⟧ r ≡ s ∣ ⟦ `fix F ⟧ s
  ∣fix-cong {{ refl }} = refl

-- data DescEq {I O : Set} : (D : IODesc I O) (r s : ISet I) (o : O) → ⟦ D ⟧ r o → ⟦ D ⟧ s o → Set₁ where
--   tt-cong    : ∀ {r s o} → DescEq `1 r s o tt tt
--   left-cong  : ∀ {A B r s o x y} → DescEq A r s o x y → DescEq (A `+ B) r s o (left x) (left y)
--   right-cong : ∀ {A B r s o x y} → DescEq B r s o x y → DescEq (A `+ B) r s o (right x) (right y)
--   ,-cong     : ∀ {A B r s o x₁ y₁ x₂ y₂} → DescEq A r s o x₁ y₁ → DescEq B r s o x₂ y₂ →
--                                            DescEq (A `* B) r s o (x₁ , x₂) (y₁ , y₂)
--   var-cong   : ∀ {i r s o x y} → x ≅ y → DescEq (`var i) r s o x y
--   !-cong     : ∀ {o′ r s o x y} → DescEq (`! o′) r s o x y
--   -- Σ-cong     : ∀ {r s o} {C : IODesc ⊥ ⊤} {p : ⟦ C ⟧ ⊥-elim tt → IODesc I O}
--   --                        {a b x y} → DescEq (`Σ p) r s o (a , x) (b , y)
--   ⟨⟩-cong    : ∀ {F r s o x y} → DescEq F (r ∣ ⟦ `fix F ⟧ r) (s ∣ ⟦ `fix F ⟧ s) o x y →
--                                  DescEq (`fix F) r s o ⟨ x ⟩ ⟨ y ⟩

-- DescEqF : {I O : Set} (D : IODesc I O) (r s : ISet I) (o : O) → ⟦ D ⟧ r o → ⟦ D ⟧ s o → Set₁
-- DescEqF D r s o x y = {{rs : r ≡ s}} → DescEq D r s o x y

-- to-≅ : ∀ {I O} {D : IODesc I O} {r s : ISet I} {o : O} {x y} →
--               {{rs : r ≡ s}} → DescEq D r s o x y → x ≅ y
-- to-≅ tt-cong = refl
-- to-≅ {{refl}} (left-cong eq) = ≅-cong left (to-≅ eq)
-- to-≅ {{refl}} (right-cong eq) = ≅-cong right (to-≅ eq)
-- to-≅ {{refl}} (,-cong eq₁ eq₂) = ≅-cong₂ _,_ (to-≅ eq₁) (to-≅ eq₂)
-- to-≅ {{refl}} (var-cong eq) = eq
-- to-≅ {x = refl} {y = refl} {{rs = refl}} !-cong = refl
-- to-≅ {{refl}} (⟨⟩-cong eq) = ≅-cong ⟨_⟩ (to-≅ eq)

-- from-≅ : ∀ {I O} {D : IODesc I O} {r s : ISet I} {o : O} {x y} →
--               {{rs : r ≡ s}} → x ≅ y → DescEq D r s o x y
-- from-≅ {D = `0} {x = ()} {{refl}} refl
-- from-≅ {D = `1} {{refl}} refl = tt-cong
-- from-≅ {D = A `+ B} {x = left x} {{refl}} refl = left-cong (from-≅ refl)
-- from-≅ {D = A `+ B} {x = right x} {{refl}} refl = right-cong (from-≅ refl)
-- from-≅ {D = A `* B} {x = (x , y)} {{refl}} refl = ,-cong (from-≅ refl) (from-≅ refl)
-- from-≅ {D = `var i} {{refl}} refl = var-cong refl
-- from-≅ {D = `! o′} {{refl}} refl = !-cong
-- -- from-≅ {D = `Σ p} {{refl}} refl = {!!}
-- -- from-≅ {D = `iso C D} {{refl}} refl = {!!}
-- from-≅ {D = `fix F} {x = ⟨ x ⟩} {{refl}} refl = ⟨⟩-cong (from-≅ refl)

-- rec-cong : ∀ {I} {D : IODesc (Either I ⊤) ⊤} {r s : ISet I} {x y} →
--            {{rs : r ≡ s}} → DescEq (`fix D) r s tt x y → DescEq (`var (right tt)) (r ∣ ⟦ `fix D ⟧ r) (s ∣ ⟦ `fix D ⟧ s) ⊤.tt x y
-- rec-cong = from-≅ ∘ to-≅

data DescEq {I O : Set} : ∀ (D : IODesc I O) {r s o} → ⟦ D ⟧ r o → ⟦ D ⟧ s o → Set₁ where
  tt-cong    : ∀ {r s o} → DescEq `1 {r} {s} {o} tt tt
  left-cong  : ∀ {A B r s o x y} → DescEq A x y → DescEq (A `+ B) {r} {s} {o} (left x) (left y)
  right-cong : ∀ {A B r s o x y} → DescEq B x y → DescEq (A `+ B) {r} {s} {o} (right x) (right y)
  ,-cong     : ∀ {A B r s o x₁ y₁ x₂ y₂} → DescEq A x₁ y₁ → DescEq B x₂ y₂ →
                                           DescEq (A `* B) {r} {s} {o} (x₁ , x₂) (y₁ , y₂)
  var-cong   : ∀ {i r s o x y} → x ≅ y → DescEq (`var i) {r} {s} {o} x y
  !-cong     : ∀ {o′ r s o x y} → DescEq (`! o′) {r} {s} {o} x y
  -- Σ-cong     : ∀ {r s o} {C : IODesc ⊥ ⊤} {p : ⟦ C ⟧ ⊥-elim tt → IODesc I O}
  --                        {a b x y} → DescEq (`Σ p) {r} {s} {o} (a , x) (b , y)
  ⟨⟩-cong    : ∀ {F r s o x y} → DescEq F x y → DescEq (`fix F) {r} {s} {o} ⟨ x ⟩ ⟨ y ⟩

DescEqF : ∀ {I O} (D : IODesc I O) {r s o} → ⟦ D ⟧ r o → ⟦ D ⟧ s o → Set₁
DescEqF D {r} {s} {o} x y = {{rs : r ≡ s}} → DescEq D {r} {s} {o} x y

DescEq-to-≅ : ∀ {I O} {D : IODesc I O} {r s o x y} →
              {{rs : r ≡ s}} → DescEq D {r} {s} {o} x y → x ≅ y
DescEq-to-≅ tt-cong = refl
DescEq-to-≅ {{refl}} (left-cong eq) = ≅-cong left (DescEq-to-≅ eq)
DescEq-to-≅ {{refl}} (right-cong eq) = ≅-cong right (DescEq-to-≅ eq)
DescEq-to-≅ {{refl}} (,-cong eq₁ eq₂) = ≅-cong₂ _,_ (DescEq-to-≅ eq₁) (DescEq-to-≅ eq₂)
DescEq-to-≅ {{refl}} (var-cong eq) = eq
DescEq-to-≅ {x = refl} {y = refl} {{rs = refl}} !-cong = refl
DescEq-to-≅ {{refl}} (⟨⟩-cong eq) = ≅-cong ⟨_⟩ (DescEq-to-≅ eq)

DescEq-from-≅ : ∀ {I O} {D : IODesc I O} {r s o x y} →
              {{rs : r ≡ s}} → x ≅ y → DescEq D {r} {s} {o} x y
DescEq-from-≅ {D = `0} {x = ()} {{refl}} refl
DescEq-from-≅ {D = `1} {{refl}} refl = tt-cong
DescEq-from-≅ {D = A `+ B} {x = left x} {{refl}} refl = left-cong (DescEq-from-≅ refl)
DescEq-from-≅ {D = A `+ B} {x = right x} {{refl}} refl = right-cong (DescEq-from-≅ refl)
DescEq-from-≅ {D = A `* B} {x = (x , y)} {{refl}} refl = ,-cong (DescEq-from-≅ refl) (DescEq-from-≅ refl)
DescEq-from-≅ {D = `var i} {{refl}} refl = var-cong refl
DescEq-from-≅ {D = `! o′} {{refl}} refl = !-cong
-- DescEq-from-≅ {D = `Σ p} {{refl}} refl = {!!}
-- DescEq-from-≅ {D = `iso C D} {{refl}} refl = {!!}
DescEq-from-≅ {D = `fix F} {x = ⟨ x ⟩} {{refl}} refl = ⟨⟩-cong (DescEq-from-≅ refl)

rec-cong : ∀ {I O} {D : IODesc (Either I O) O} {r s o x y} →
           {{rs : r ≡ s}} → DescEq (`fix D) x y → DescEq (`var (right o)) {r ∣ ⟦ `fix D ⟧ r} {s ∣ ⟦ `fix D ⟧ s} {o} x y
rec-cong = DescEq-from-≅ ∘ DescEq-to-≅
