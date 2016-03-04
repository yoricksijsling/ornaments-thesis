module ContextFree.Multi.Examples.List where

open import Common
open import ContextFree.Multi.Desc
open import ContextFree.Multi.Quotable

infixr 5 _∷_

data ListP (A : Set) : Set where
  [] : ListP A
  _∷_ : A → ListP A → ListP A

pattern nil-α = []
pattern nil-β = ⟨ left tt ⟩
pattern cons-α x xs = x ∷ xs
pattern cons-β x xs = ⟨ right (left (x , xs , tt)) ⟩
pattern absurd-β = ⟨ right (right ()) ⟩

module Manually where
  -- Description of lists in our Desc universe. The extra `1 and `0 are not
  -- strictly necessary but make the structure of the sum-of-products more
  -- regular, which will be useful later.
  desc : IODesc (Either (Fin 1) ⊤) ⊤
  desc = `1 `+ (`var (left 0) `* `var (right tt) `* `1) `+ `0

  req : (A : Set) → ISet (Fin 1)
  req A zero = A
  req A (suc ())
  
  -- Embedding-projection pair and proofs
  to : (A : Set) → ListP A → ⟦ `fix desc ⟧ (req A) tt
  to A nil-α = nil-β
  to A (cons-α x xs) = cons-β x (to A xs)

  from : (A : Set) → ⟦ `fix desc ⟧ (req A) tt → ListP A
  from A nil-β = []
  from A (cons-β x xs) = cons-α x (from A xs)
  from A absurd-β

  to-from : (A : Set) → ∀ x → from A (to A x) ≡ x
  to-from A nil-α = refl
  to-from A (cons-α x xs) = cong (λ xs′ → cons-α x xs′) (to-from A xs)

  from-to : (A : Set) → ∀ x → to A (from A x) ≡ x
  from-to A nil-β = refl
  from-to A (cons-β x xs) = cong (λ xs′ → cons-β x xs′) (from-to A xs)
  from-to A absurd-β

  rec : ∀ A → Quotable (ListP A)
  rec A = record { desc = desc ; to = to A ; from = from A
                 ; to-from = to-from A ; from-to = from-to A }


-- Our goal is to generate the Quotable record automatically from just the
-- definition of ListP. First we look at the datatype and generate an
-- intermediate representation of the datatype which is 'safe' in the sense
-- that it can always be converted to a Desc.

open import ContextFree.Multi.Quoted
open import ContextFree.Multi.Quoting

nsdt : NamedSafeDatatype
nsdt = quoteDatatypeᵐ ListP

sdt : SafeDatatype
sdt = fst $ unnameSafeDatatype $ nsdt

module TestQdt where
  open import Builtin.Reflection
  open import ContextFree.Multi.Params
  test-nsdt : nsdt ≡ mk (quote ListP) 1 (param₀ visible "A" ∷ [])
                        ((quote ListP.[]  , []) ∷
                         (quote ListP._∷_ , Spar 0 ∷ Srec ∷ []) ∷
                         [])
  test-nsdt = refl

  test-sdt : sdt ≡ mk 1 (param₀ visible "A" ∷ [])
                        ([] ∷
                         (Spar 0 ∷ Srec ∷ []) ∷
                         [])
  test-sdt = refl

-- The description can easily be calculated from the NamedSafeDatatype

module TestDesc where
  test-desc : safeDatatypeToDesc sdt ≡ Manually.desc
  test-desc = refl

-- Unquote a record which contains the Desc and the embedding-projection pair.

unquoteDecl qrec = defineRecord qrec nsdt

--

module TestQrec (A : Set) where
  module Q = RawQuotable (qrec A)
  module M = Quotable (Manually.rec A)

  test-desc : Q.desc ≡ M.desc
  test-desc = refl

  test-req : (i : Fin 1) → Q.req i ≡ M.req i
  test-req zero = refl
  test-req (suc ())

  test-to : {{rs : Q.req ≡ M.req}} → ∀ x → DescEq (`fix Q.desc) (Q.to x) (M.to x)
  test-to [] = ⟨⟩-cong (left-cong tt-cong)
  test-to (x ∷ xs) = ⟨⟩-cong $ right-cong $ left-cong $
                     ,-cong (var-cong refl) $ ,-cong (var-cong (DescEq-to-≅ (test-to xs))) $ tt-cong
  
  test-from : {{rs : Q.req ≡ M.req}} → ∀ {x y} → DescEq (`fix Q.desc) x y → Q.from x ≅ M.from y
  test-from (⟨⟩-cong (left-cong tt-cong)) = refl
  test-from (⟨⟩-cong (right-cong (left-cong (,-cong (var-cong refl) (,-cong (var-cong eq) tt-cong))))) = ≅-cong (_∷_ _) (test-from (DescEq-from-≅ eq))
  test-from (⟨⟩-cong (right-cong (right-cong ())))

-- -- As an inverse of quoteDatatypeᵐ, we want to be able to define a datatype
-- -- for a given SafeDatatype.

-- open import ContextFree.Multi.Unquoting

-- -- The definition of the datatype can be partially automated. The types of the
-- -- constructors can be unquoted.
-- data ListP′ (A : Set) : Set where
--   [] : sdt as ListP′ ∋ 0    -- ListP A
--   _∷_ : sdt as ListP′ ∋ 1   -- A → ListP A → ListP A

