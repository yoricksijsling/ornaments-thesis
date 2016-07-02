
module Presentation where

open import Common

-- Most stuff for the presentation can be taken from Thesis/Introduction.agda

open import Cx.Named

natDesc : DatDesc ε ε _
natDesc = ι (λ γ → tt)
  ⊕ "n" /rec (λ γ → tt) ⊗ ι (λ γ → tt)
  ⊕ `0

listDesc : DatDesc ε (ε ▷₁′ Set) _
listDesc = ι (λ γ → tt)
  ⊕ "x" / (λ γ → top γ)
  ⊗ "xs" /rec (λ γ → tt)
  ⊗ ι (λ γ → tt)
  ⊕ `0

vecDesc : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
vecDesc = ι (λ γ → (tt , 0))
  ⊕ "n" / (λ γ → Nat)
  ⊗ "x" / (λ γ → top (pop γ))
  ⊗ "xs" /rec (λ γ → tt , top (pop γ))
  ⊗ ι (λ γ → tt , suc (top (pop γ)))
  ⊕ `0



-- open import Common hiding (_&_)

-- -- Sorted lists
-- data SList (A : Set) {{R : Ord A}} : (lowest : A) → Set where
--   [] : ∀{v} → SList A v
--   _∷_ : ∀{v} → (x : A) → SList A v → {{p : IsTrue (x ≤? v)}} → SList A x


-- module SimpleDescriptions where
--   open import Cx.Simple

--   natDesc : DatDesc 2
--   natDesc = ι
--     ⊕ rec-⊗ ι
--     ⊕ `0

--   nat-to : Nat → μ natDesc
--   nat-to zero = ⟨ 0 , tt ⟩
--   nat-to (suc n) = ⟨ 1 , nat-to n , tt ⟩

--   data StringList : Set where
--     [] : StringList
--     _∷_ : String → StringList → StringList

--   stringListDesc : DatDesc 2
--   stringListDesc = ι
--     ⊕ (λ γ → String) ⊗ rec-⊗ ι
--     ⊕ `0

--   nat→stringlist : DatOrn natDesc
--   nat→stringlist = ι
--     ⊕ (λ _ → String) +⊗ rec-⊗ ι
--     ⊕ `0

--   t : ornToDesc nat→stringlist ≡ stringListDesc
--   t = refl

-- module ExtendedDescriptions where
--   open import Cx.Extended
  

-- open import Cx.HasDesc
-- open import Cx.GenericOperations
-- open import Cx.Unquoting

-- ----------------------------------------
-- -- HTML fragments

-- data Html : Set where
--   text : (text : String) → Html
--   conc : Html → Html → Html
--   div : Html → Html
--   p : Html → Html

-- unquoteDecl quotedHtml HtmlHasDesc =
--   deriveHasDesc quotedHtml HtmlHasDesc (quote Html)

-- htmlDesc : DatDesc ε ε _
-- htmlDesc = QuotedDesc.desc quotedHtml

-- --------------------

-- d1 : gdepth (div (text "test")) ≡ 1
-- d1 = refl

-- d2 : gdepth (p (div (text "test"))) ≡ 2
-- d2 = refl

-- d3 : gdepth (div (p (conc (text "one") (text "two")))) ≡ 3
-- d3 = refl

-- c1 : gcount (div (text "test")) ≡ 2
-- c1 = refl

-- c2 : gcount (p (div (text "test"))) ≡ 3
-- c2 = refl

-- c3 : gcount (div (p (conc (text "one") (text "two")))) ≡ 5
-- c3 = refl

-- --------------------

-- data ContentModel : Set where
--   phrasing : ContentModel
--   flow : ContentModel

-- _∪_ : ContentModel → ContentModel → ContentModel
-- phrasing ∪ phrasing = phrasing
-- x ∪ y = flow

-- eqContentModel : (x : ContentModel) → (y : ContentModel) → Dec (x ≡ y)
-- eqContentModel phrasing phrasing = yes refl
-- eqContentModel phrasing flow = no (λ ())
-- eqContentModel flow phrasing = no (λ ())
-- eqContentModel flow flow = yes refl

-- instance
--   EqContentModel : Eq ContentModel
--   EqContentModel = record { _==_ = eqContentModel }

-- --------------------

-- data HtmlView (X : ⊤′ → Set) : ⟦ htmlDesc ⟧ tt X tt → Set where
--   `text : ∀ s → HtmlView X (0 , s , refl)
--   `conc : ∀ cm1 cm2 → HtmlView X (1 , cm1 , cm2 , refl)
--   `div : ∀ cm → HtmlView X (2 , cm , refl)
--   `p : ∀ cm → HtmlView X (3 , cm , refl)

-- htmlView : ∀{X} (v : ⟦ htmlDesc ⟧ tt X tt) → HtmlView X v
-- htmlView (zero , s , refl) = `text s
-- htmlView (suc zero , cm1 , cm2 , refl) = `conc cm1 cm2
-- htmlView (suc (suc zero) , cm , refl) = `div cm
-- htmlView (suc (suc (suc zero)) , cm , refl) = `p cm
-- htmlView (suc (suc (suc (suc ()))) , _)

-- htmlUnview : ∀{X v} → HtmlView X v → ⟦ htmlDesc ⟧ tt X tt
-- htmlUnview {v = v} _ = v

-- cmAlg : Alg htmlDesc tt (λ i → Maybe ContentModel)
-- cmAlg x with htmlView x
-- cmAlg _ | `text s = just phrasing
-- cmAlg _ | `conc cm1 cm2 = _∪_ <$> cm1 <*> cm2
-- cmAlg _ | `div cm = flow <$ cm
-- cmAlg _ | `p cm = guardA (cm == just phrasing) (just flow)

-- {-
-- pattern `text = zero
-- pattern `conc = suc zero
-- pattern `div = suc (suc zero)
-- pattern `p = suc (suc (suc zero))
-- pattern `nohtml = suc (suc (suc (suc ())))

-- cmAlg : Alg htmlDesc tt (λ i → Maybe ContentModel)
-- cmAlg (`text , s , refl) = just phrasing
-- cmAlg (`conc , cm1 , cm2 , refl) = _∪_ <$> cm1 <*> cm2
-- cmAlg (`div , cm , refl) = flow <$ cm
-- cmAlg (`p , cm , refl) = guardA (cm == just phrasing) (just flow)
-- cmAlg (`nohtml , _)
-- -}

-- calculateCM : Html → Maybe ContentModel
-- calculateCM = gfold cmAlg

-- cm1 : calculateCM (div (text "test"))
--   ≡ just flow
-- cm1 = refl

-- cm2 : calculateCM (p (div (text "test")))
--   ≡ nothing
-- cm2 = refl

-- cm3 : calculateCM (div (p (conc (text "one") (text "two"))))
--   ≡ just flow
-- cm3 = refl

-- --------------------

-- html-addCM : Orn (ε ▷′ Maybe ContentModel) (λ i → tt) ε id htmlDesc
-- html-addCM = algOrn cmAlg

-- htmlCMDesc : DatDesc (ε ▷′ Maybe ContentModel) ε _
-- htmlCMDesc = ornToDesc html-addCM

-- -- data HtmlCM : (pf : Maybe ContentModel) → Set where
-- --   text : (text : String) → HtmlCM (just phrasing)
-- --   conc : ∀ cm1 → HtmlCM cm1 → ∀ cm2 → HtmlCM cm2 → HtmlCM (_∪_ <$> cm1 <*> cm2)
-- --   div : ∀ cm → HtmlCM cm → HtmlCM (flow <$ cm)
-- --   p : ∀ cm → HtmlCM cm → HtmlCM (guardA (cm == just phrasing) (just flow))

-- data HtmlCM : unquoteDat htmlCMDesc where
--   text : unquoteCon htmlCMDesc 0 HtmlCM
--   conc : unquoteCon htmlCMDesc 1 HtmlCM
--   div : unquoteCon htmlCMDesc 2 HtmlCM
--   p : unquoteCon htmlCMDesc 3 HtmlCM

-- unquoteDecl quotedHtmlCM HtmlCMHasDesc =
--   deriveHasDescExisting quotedHtmlCM HtmlCMHasDesc
--   (quote HtmlCM) htmlCMDesc


-- htmlcm1 : HtmlCM (just flow)
-- htmlcm1 = div _ (text "test")

-- htmlcm2 : HtmlCM nothing
-- htmlcm2 = p _ (div _ (text "test"))

-- htmlcm3 : HtmlCM (just flow)
-- htmlcm3 = div _ (p _ (conc _ (text "one") _ (text "two")))


-- htmlcm-to-html : ∀{cm} → HtmlCM cm → Html
-- htmlcm-to-html = gforget html-addCM

