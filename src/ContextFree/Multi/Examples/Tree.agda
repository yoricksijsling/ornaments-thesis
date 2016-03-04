module ContextFree.Multi.Examples.Tree where

open import Common
open import ContextFree.Multi.Desc
open import ContextFree.Multi.DescEquality
open import ContextFree.Multi.DescFunction
open import ContextFree.Multi.EmbeddingProjection
open import ContextFree.Multi.Quoted
open import ContextFree.Multi.Quoting

data Tree (A : Set) : Set where
  leaf : Tree A
  node1 : A → Tree A → Tree A
  node2 : A → Tree A → Tree A → Tree A

pattern leaf-α = leaf
pattern leaf-β = ⟨ left tt ⟩
pattern node1-α v xs = node1 v xs
pattern node1-β v xs = ⟨ right (left (v , xs , tt)) ⟩
pattern node2-α v xs ys = node2 v xs ys
pattern node2-β v xs ys = ⟨ right (right (left (v , xs , ys , tt))) ⟩
pattern absurd-β = ⟨ right (right (right ())) ⟩

module Manually where
  desc : IODesc (Either (Fin 1) ⊤) ⊤
  desc = `1 `+ (`var (left 0) `* `var (right tt) `* `1) `+ (`var (left 0) `* `var (right tt) `* `var (right tt) `* `1) `+ `0

  req : (A : Set) → ISet (Fin 1)
  req A zero = A
  req A (suc ())

  to : (A : Set) → Tree A → ⟦ `fix desc ⟧ (req A) tt
  to A leaf-α = leaf-β
  to A (node1-α v xs) = node1-β v (to A xs)
  to A (node2-α v xs ys) = node2-β v (to A xs) (to A ys)

  from : (A : Set) → ⟦ `fix desc ⟧ (req A) tt → Tree A
  from A leaf-β = leaf-α
  from A (node1-β v xs) = node1-α v (from A xs)
  from A (node2-β v xs ys) = node2-α v (from A xs) (from A ys)
  from A absurd-β

  to-from : (A : Set) → ∀ x → from A (to A x) ≡ x
  to-from A leaf-α = refl
  to-from A (node1-α v xs) = cong (node1-α v) (to-from A xs)
  to-from A (node2-α v xs ys) = cong₂ (node2-α v) (to-from A xs) (to-from A ys)

  from-to : (A : Set) → ∀ x → to A (from A x) ≡ x
  from-to A leaf-β = refl
  from-to A (node1-β v xs) = cong (node1-β v) (from-to A xs)
  from-to A (node2-β v xs ys) = cong₂ (node2-β v) (from-to A xs) (from-to A ys)
  from-to A absurd-β

  rec : ∀ A → IsContextFree (Tree A)
  rec A = record { desc = desc ; to = to A ; from = from A
                 ; to-from = to-from A ; from-to = from-to A }


nsdt : NamedSafeDatatype
nsdt = quoteDatatypeᵐ Tree

module TestNsdt where
  open import Builtin.Reflection
  open import ContextFree.Multi.Params
  test-nsdt : nsdt ≡ mk (quote Tree) 1 (param₀ visible "A" ∷ [])
                      ((quote leaf , []) ∷
                       (quote node1 , Spar 0 ∷ Srec ∷ []) ∷
                       (quote node2 , Spar 0 ∷ Srec ∷ Srec ∷ []) ∷
                       [])
  test-nsdt = refl

unquoteDecl qrec = defineRecord qrec nsdt

module TestQrec (A : Set) where
  module Q = RawIsContextFree (qrec A)
  module M = IsContextFree (Manually.rec A)

  test-desc : Q.desc ≡ M.desc
  test-desc = refl

  test-req : ∀ i → Q.req i ≡ M.req i
  test-req zero = refl
  test-req (suc ())

  test-to : {{rs : Q.req ≡ M.req}} → ∀ x → DescEq (`fix Q.desc) (Q.to x) (M.to x)
  test-to leaf = ⟨⟩-cong (left-cong tt-cong)
  test-to (node1 x xs) = ⟨⟩-cong $ right-cong $ left-cong $
                         ,-cong (var-cong refl) $
                         ,-cong (var-cong (DescEq-to-≅ (test-to xs))) $
                         tt-cong
  test-to (node2 x xs ys) = ⟨⟩-cong $ right-cong $ right-cong $ left-cong $
                            ,-cong (var-cong refl) $
                            ,-cong (var-cong (DescEq-to-≅ (test-to xs))) $
                            ,-cong (var-cong (DescEq-to-≅ (test-to ys))) $
                            tt-cong

  test-from : {{rs : Q.req ≡ M.req}} → ∀ {x y} → DescEq (`fix Q.desc) x y → Q.from x ≅ Q.from y
  test-from (⟨⟩-cong (left-cong tt-cong)) = refl
  test-from (⟨⟩-cong (right-cong (left-cong
    (,-cong (var-cong refl) (,-cong (var-cong refl) tt-cong))))) = refl
  test-from (⟨⟩-cong (right-cong (right-cong (left-cong
    (,-cong (var-cong refl) (,-cong (var-cong refl) (,-cong (var-cong refl) tt-cong))))))) = refl
  test-from (⟨⟩-cong (right-cong (right-cong (right-cong ()))))
