%include thesis.fmt

\chapter{Ornaments on families of datatypes}\label{chap:extended}

With indices. Show how mutual recursion is the same as indices.

Quick example of usage of 'extended' descriptions and their ornaments

\section{Descriptions}

\begin{codelst}{Descriptions of families of datatypes}{ext-description}\begin{code}
data ConDesc (I : Cx₀) : (Γ : Cx₁) → Set₁ where
  ι : ∀{Γ} → (o : (γ : ⟦ Γ ⟧) → ⟦ I ⟧) → ConDesc I Γ
  _⊗_ : ∀{Γ} → (S : (γ : ⟦ Γ ⟧) → Set) → (xs : ConDesc I (Γ ▷ S)) → ConDesc I Γ
  rec_⊗_ : ∀{Γ} → (i : (γ : ⟦ Γ ⟧) → ⟦ I ⟧) → (xs : ConDesc I Γ) → ConDesc I Γ

data DatDesc (I : Cx)(Γ : Cx) : (#c : Nat) → Set₁ where
  `0 : DatDesc I Γ 0
  _⊕_ : ∀{#c}(x : ConDesc I Γ)(xs : DatDesc I Γ #c) → DatDesc I Γ (suc #c)
\end{code}\end{codelst}

In the previous sections we have written many functions for |ConDesc|
and |DatDesc| separately. Especially now that the types of those functions grow more
complicated this becomes a nuisance. The current |ConDesc| and
|DatDesc| have some overlapping arguments; they both require the |I|
and |Γ| contexts. This fact can be exploited by writing a small
universe for |ConDesc| and |DatDesc|. Now we can reference both of
them with |Desc I Γ dt|, where |dt| can be either |isCon| or |isDat
#c|.

\begin{code}
data DescTag : Set₂ where
  isCon : DescTag
  isDat : (#c : Nat) → DescTag

Desc : (I : Cx) → (Γ : Cx) → DescTag → Set₁
Desc I Γ (isCon) = ConDesc I Γ
Desc I Γ (isDat #c) = DatDesc I Γ #c
\end{code}

\begin{code}
⟦_⟧desc : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → Pow ⟦ I ⟧ → Pow ⟦ I ⟧
⟦_⟧desc {dt = isCon} (ι o) γ X o′ = o γ ≡ o′
⟦_⟧desc {dt = isCon} (S ⊗ xs) γ X o = Σ (S γ) λ s → ⟦ xs ⟧desc (γ , s) X o
⟦_⟧desc {dt = isCon} (rec i ⊗ xs) γ X o = X (i γ) × ⟦ xs ⟧desc γ X o
⟦_⟧desc {dt = isDat #c} D γ X o = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧desc γ X o
\end{code}

\begin{code}
data μ {I Γ #c} (F : DatDesc I Γ #c) (γ : ⟦ Γ ⟧) (o : ⟦ I ⟧) : Set where
  ⟨_⟩ : ⟦ F ⟧ γ (μ F γ) o → μ F γ o
\end{code}

\begin{code}
descmap : ∀{I Γ dt X Y} (f : ∀{i : ⟦ I ⟧} → X i → Y i) (D : Desc I Γ dt) →
          ∀{γ i} → ⟦ D ⟧ γ X i → ⟦ D ⟧ γ Y i
\end{code}

\begin{code}
Alg : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → Pow ⟦ I ⟧ → Set
Alg {I} D γ X = {i : ⟦ I ⟧} → ⟦ D ⟧ γ X i → X i
\end{code}

\begin{code}
fold : ∀{I Γ #c}{D : DatDesc I Γ #c}{γ X} (α : Alg D γ X) →
       {i : ⟦ I ⟧} → μ D γ i → X i
fold {D = D} α ⟨ xs ⟩ = α (descmap (fold α) D xs)
\end{code}

\section{Ornaments}

\begin{codelst}{Ornaments for families of datatypes}{ext-ornament}\begin{code}
data Orn {I J}(u : Cxf J I) : ∀{Γ Δ dt} (c : Cxf Δ Γ) (D : Desc I Γ dt) → Set₁ where
  ι : ∀{Γ Δ i}{c : Cxf Δ Γ} → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) → Orn u c (ι i)
  -⊗_ : ∀{Γ Δ S xs}{c : Cxf Δ Γ} → (xs⁺ : Orn u (cxf-both c) xs) → Orn u c (S ⊗ xs)
  rec_⊗_ : ∀{Γ Δ i xs}{c : Cxf Δ Γ} →
            (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) → (xs⁺ : Orn u c xs) → Orn u c (rec i ⊗ xs)

  _+⊗_ : ∀{Γ Δ}{c : Cxf Δ Γ}{xs : ConDesc I Γ} →
                (S : (δ : ⟦ Δ ⟧) → Set) → (xs⁺ : Orn u (cxf-forget c S) xs) → Orn u c xs
  rec_+⊗_ : ∀{Γ Δ}{c : Cxf Δ Γ}{xs : ConDesc I Γ} →
                  (j : (δ : ⟦ Δ ⟧) → ⟦ J ⟧) → (xs⁺ : Orn u c xs) → Orn u c xs
  give-K : ∀{Γ Δ S xs}{c : Cxf Δ Γ} →
           (s : (δ : ⟦ Δ ⟧) → S (c δ)) → (xs⁺ : Orn u (cxf-instantiate c s) xs) → Orn u c (S ⊗ xs)

  `0 : ∀{Γ Δ}{c : Cxf Δ Γ} → Orn u c `0
  _⊕_ : ∀{Γ Δ #c x}{c : Cxf Δ Γ}{xs : DatDesc I Γ #c} →
         (x⁺ : Orn u c x) (xs⁺ : Orn u c xs) → Orn u c (x ⊕ xs)
\end{code}\end{codelst}

\begin{codelst}{Interpretation of ornaments}{ext-orntodesc}\begin{code}
module _ {I J}{u : Cxf J I} where
  ornToDesc : ∀{Γ Δ dt}{c : Cxf Δ Γ}{D : Desc I Γ dt} → (o : Orn u c D) → Desc J Δ dt
  ornToDesc {c = c} (ι j) = ι (uninv ∘ j)
  ornToDesc (-⊗_ {S = S} {c = c} xs⁺) = S ∘ c ⊗ ornToDesc xs⁺
  ornToDesc (rec j ⊗ xs⁺) = rec (uninv ∘ j) ⊗ ornToDesc xs⁺
  ornToDesc (_+⊗_ S xs⁺) = S ⊗ ornToDesc xs⁺
  ornToDesc (rec_+⊗_ j xs⁺) = rec j ⊗ ornToDesc xs⁺
  ornToDesc (give-K s xs⁺) = ornToDesc xs⁺
  ornToDesc `0 = `0
  ornToDesc (x⁺ ⊕ xs⁺) = ornToDesc x⁺ ⊕ ornToDesc xs⁺
\end{code}\end{codelst}

\begin{codelst}{Ornamental algebras}{ext-forget}\begin{code}
module _ {I J}{u : Cxf J I} where
  forgetNT : ∀{Γ Δ dt}{c : Cxf Δ Γ}{D : Desc I Γ dt} (o : Orn u c D) →
             ∀ {δ X j} → ⟦ o ⟧ δ (X ∘ u) j → ⟦ D ⟧ (c δ) X (u j)
  forgetNT {c = c} (ι j) {δ} refl = sym (inv-eq (j δ))
  forgetNT (-⊗ xs⁺) (s , v) = s , forgetNT xs⁺ v
  forgetNT (rec j ⊗ xs⁺) {δ} {X} (s , v) = transport X (inv-eq (j δ)) s , forgetNT xs⁺ v
  forgetNT (_+⊗_ S xs⁺) (s , v) = forgetNT xs⁺ v
  forgetNT (rec_+⊗_ j xs⁺) (s , v) = forgetNT xs⁺ v
  forgetNT (give-K s xs⁺) {δ} v = s δ , forgetNT xs⁺ v
  forgetNT `0 (() , _)
  forgetNT (x⁺ ⊕ xs⁺) (zero , v) = zero , forgetNT x⁺ v
  forgetNT (x⁺ ⊕ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

  forgetAlg : ∀{Γ Δ #c}{c : Cxf Δ Γ}{D : DatDesc I Γ #c} (o : Orn u c D) →
              ∀{δ} → Alg (ornToDesc o) δ (μ D (c δ) ∘ u)
  forgetAlg o = ⟨_⟩ ∘ forgetNT o

  forget : ∀{Γ Δ #c}{c : Cxf Δ Γ}{D : DatDesc I Γ #c} (o : Orn u c D) →
           ∀{δ j} → μ (ornToDesc o) δ j → μ D (c δ) (u j)
  forget o = fold (forgetAlg o)
\end{code}\end{codelst}

\begin{example}
For
example: we could consider a datatype which holds login information,
where a value of this type contains a domain name, username and
password:

\begin{code}
loginDesc : DatDesc 1
loginDesc = Uri ⊗ Name ⊗ Password ⊗ ι ⊕ `0
\end{code}

Say this is part of some personal password management system. One of
the use cases is to find your login information for a given uri. Now
what if some function always returns login information for the same
uri?
\end{example}

\section{Algebraic ornaments}

Interestingly, algebraic ornaments only work when the Algebra is
polymorphic in the datatype parameters. That is because during the
definition of datatypes we do not know the values of the parameters,
and by extension we do not know them in an ornament.

\begin{codelst}{Algebraic ornaments}{ext-algorn}\begin{code}
  algOrn′ : ∀{Γ Δ dt}{c : Cxf Δ Γ}(D : Desc I Γ dt) →
           (∀{δ : ⟦ Δ ⟧} → Alg D (c δ) J) → DefOrn (I ▷ J) (pop) Δ c D
  algOrn′ {dt = isCon} {c = c} (ι o) α = ι (λ δ → inv (o (c δ) , α refl))
  algOrn′ {dt = isCon} (S ⊗ xs) α = -⊗ (algOrn′ xs (λ {γ} → curry α (top γ)))
  algOrn′ {dt = isCon} {c = c} (rec i ⊗ xs) α = J ∘ i ∘ c
                                            +⊗ rec (λ δ → inv (i (c (pop δ)) , top δ))
                                             ⊗ algOrn′ xs (λ {δ} → curry α (top δ))
  algOrn′ {dt = isDat _} `0 α = `0
  algOrn′ {dt = isDat _} (x ⊕ xs) α = algOrn′ x (curry α 0) ⊕ algOrn′ xs (α ∘ (suc *** id))

  algOrn : ∀{Γ dt}{D : Desc I Γ dt} →
           ({γ : ⟦ Γ ⟧} → Alg D γ J) → DefOrn (I ▷ J) pop Γ id D
  algOrn {D = D} = algOrn′ D
\end{code}\end{codelst}

\section{Reornaments}

\begin{code}
module _ {I J K}{u : Cxf J I}{v : Cxf K J} where
  _>>⁺_ : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
          (o : Orn u c D) → Orn v d (ornToDesc o) → Orn (u ∘ v) (c ∘ d) D
\end{code}

To prove that composition is sound we show that the right description is
returned. The descriptions contain higher order terms so we use
extensionality to compare them.
\begin{code}
  module _ (ext : ∀{a b} → Extensionality a b) where
    >>⁺-coherence : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
                    (o : Orn u c D) → (p : Orn v d (ornToDesc o)) →
                    (ornToDesc (o >>⁺ p)) ≡ ornToDesc p
\end{code}

Reornaments currently only work when the original datatype does not have
parameters. To make it work for all datatypes, the indices have to be
dependent on the parameters. (See handwritten notes)

\begin{code}
reornament : ∀{I J Δ}{u : Cxf J I}{c : Cxf Δ ε}{#c}{D : DatDesc I ε #c} →
             (o : Orn u c D) → Orn (u ∘ pop) c D
reornament o = o >>⁺ (algOrn (λ {δ} → forgetAlg o {δ}))
\end{code}

\section{Discussion}

\begin{itemize}
\item Indices can't be dependent on parameters right now. Show what
  the problem is and how it can potentially be solved.
\end{itemize}
