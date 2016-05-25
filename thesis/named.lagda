%include thesis.fmt

\chapter{Ornaments on reflected datatypes}\label{chap:named}

Usage of quoting. Show how the names fit into descriptions. Also show
|dumpDatatype|?

\section{Descriptions and ornaments}

The changes to the descriptions are fairly small. The only difference
is that each argument can now contain a name of type string. The full
definition of descriptions is given in Listing
\ref{lst:named-description}. The name
is added in front of all the relevant constructors, separated by a
slash.

\begin{codelst}{Descriptions with names}{named-description}\begin{code}
data ConDesc (I : Cx₀) : (Γ : Cx₁) → Set₁ where
  ι : ∀{Γ} → (o : (γ : ⟦ Γ ⟧) → ⟦ I ⟧) → ConDesc I Γ
  _/_⊗_ : ∀{Γ} → (nm : String) → (S : (γ : ⟦ Γ ⟧) → Set) → (xs : ConDesc I (Γ ▷ S)) → ConDesc I Γ
  _/rec_⊗_ : ∀{Γ} → (nm : String) → (i : (γ : ⟦ Γ ⟧) → ⟦ I ⟧) → (xs : ConDesc I Γ) → ConDesc I Γ
data DatDesc (I : Cx)(Γ : Cx) : (#c : Nat) → Set₁ where
  `0 : DatDesc I Γ 0
  _⊕_ : ∀{#c} → (x : ConDesc I Γ) → (xs : DatDesc I Γ #c) → DatDesc I Γ (suc #c)
\end{code}\end{codelst}

Ornaments are changed accordingly. The copying and insertion operators
all require a name. The definition of ornaments is in Listing \ref{lst:named-ornament}.

\begin{codelst}{Ornaments with names}{named-ornament}\begin{code}
data Orn {I J}(u : Cxf J I) : ∀{Γ Δ dt} (c : Cxf Δ Γ) (D : Desc I Γ dt) → Set₁ where
  ι : ∀{Γ Δ i}{c : Cxf Δ Γ} → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) → Orn u c (ι i)
  _/-⊗_ : ∀{Γ Δ nm S xs}{c : Cxf Δ Γ} → (nm′ : String) →
          (xs⁺ : Orn u (cxf-both c) xs) → Orn u c (nm / S ⊗ xs)
  _/rec_⊗_ : ∀{Γ Δ nm i xs}{c : Cxf Δ Γ} → (nm′ : String) →
             (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) → (xs⁺ : Orn u c xs) → Orn u c (nm /rec i ⊗ xs)

  _/_+⊗_ : ∀{Γ Δ}{c : Cxf Δ Γ}{xs : ConDesc I Γ} →
            (nm : String) (S : (δ : ⟦ Δ ⟧) → Set) (xs⁺ : Orn u (cxf-forget c S) xs) → Orn u c xs
  _/rec_+⊗_ : ∀{Γ Δ}{c : Cxf Δ Γ}{xs : ConDesc I Γ} →
               (nm : String) (j : (δ : ⟦ Δ ⟧) → ⟦ J ⟧) (xs⁺ : Orn u c xs) → Orn u c xs
  give-K : ∀{Γ Δ S xs nm}{c : Cxf Δ Γ} →
           (s : (δ : ⟦ Δ ⟧) → S (c δ)) →
           (xs⁺ : Orn u (cxf-instantiate c s) xs) →
           Orn u c (nm / S ⊗ xs)

  `0 : ∀{Γ Δ}{c : Cxf Δ Γ} → Orn u c `0
  _⊕_ : ∀{Γ Δ #c x}{c : Cxf Δ Γ}{xs : DatDesc I Γ #c}
         (x⁺ : Orn u c x) (xs⁺ : Orn u c xs) → Orn u c (x ⊕ xs)
\end{code}\end{codelst}

\section{Results of the quoting of a datatype}

Real datatype definitions also contain the names for the datatype and
the constructors. When a datatype is quoted we want to keep this
information. Additionally, the quoting of a datatype results in a
|DatDesc I Γ #c|, but we do not know \emph{which} |I|, |Γ| and
|#c|. We define a |QuotedDesc| record (Listing \ref{lst:quoteddesc},
which can contain all the information which we can extract from a
datatype definition including the indices, parameters, constructor
count, names and description.

\begin{codelst}{Quoted descriptions}{quoteddesc}\begin{code}
record QuotedDesc : Set₂ where
  constructor mk
  field
    {I} : Cx
    {Γ} : Cx
    {#c} : Nat
    `datatypeName : Name
    `constructorNames : Vec Name #c
    desc : DatDesc I Γ #c
\end{code}\end{codelst}

The |HasDesc| record (Listing \ref{lst:hasdesc}) contains an
embedding-projection pair for a certain type. The type on which it
works is passed as a parameter and has to be fully applied; so an
embedding-projection pair for |Vec| is of type |HasDesc (Vec A n)|,
for a specific |A| and |n|.

\begin{codelst}{HasDesc definition}{hasdesc}\begin{code}
record HasDesc (A : Set) : Set₂ where
  constructor mk
  field
    {I Γ} : Cx
    {#c} : Nat
    desc : DatDesc I Γ #c
    {γ} : ⟦ Γ ⟧
    {i} : ⟦ I ⟧
    to′ : A → μ desc γ i
    from′ : μ desc γ i → A
\end{code}\end{codelst}

The |HasDesc| record is supposed to be used as an instance, so:

\begin{code}
to : {A : Set} ⦃r : HasDesc A⦄ → A → μ (desc r) (γ r) (i r)
to ⦃r⦄ = to′ r
from : {A : Set} ⦃r : HasDesc A⦄ → μ (desc r) (γ r) (i r) → A
from ⦃r⦄ = from′ r
\end{code}

\begin{example}
\begin{code}
unquoteDecl quotedVec vecHasDesc =
  deriveHasDesc quotedVec vecHasDesc (quote Vec)
\end{code}

\begin{code}
quotedVec : QuotedDesc

vecHasDesc : {A : Set} {n : Nat} → HasDesc (Vec A n)

vecto : ∀{A n} → Vec A n → μ vecDesc (tt , A) (tt , n)
vecto = to
\end{code}

\end{example}

\section{Generic functions and algebras}

Some of the operations on descriptions and ornaments can be lifted to
work on real datatypes.

\begin{code}
fold : ∀{I Γ #c}{D : DatDesc I Γ #c}{γ X} (α : Alg D γ X) →
  {i : ⟦ I ⟧} → μ D γ i → X i
gfold : ∀{A}⦃R : HasDesc A⦄ → ∀{X} → Alg (desc R) (γ R) X → A → X (i R)
gfold α = fold α ∘ to
\end{code}

\section{More ornament combinators}

Algebraic ornaments, composition (|>>⁺|) and reornament may be
considered as ornament combinators.

\begin{code}
idOrn : ∀{I Γ Δ dt c}{D : Desc I Γ dt} → DefOrn I id Δ c D
idOrn {dt = isCon} {c} {ι o} = ι (λ δ → inv (o (c δ)))
idOrn {dt = isCon} {c} {nm / S ⊗ xs} = nm /-⊗ idOrn
idOrn {dt = isCon} {c} {nm /rec i ⊗ xs} = nm /rec (λ δ → inv (i (c δ))) ⊗ idOrn
idOrn {dt = isDat _} {c} {`0} = `0
idOrn {dt = isDat _} {c} {x ⊕ xs} = idOrn ⊕ idOrn
\end{code}

\begin{code}
updateConstructor : ∀{I Γ #c}{D : DatDesc I Γ #c} → (k : Fin #c) →
                    ∀{Δ c} → DefOrn I id Δ c (lookupCtor D k) →
                    DefOrn I id Δ c D
updateConstructor {D = `0} () o
updateConstructor {D = x ⊕ xs} zero o = o ⊕ idOrn
updateConstructor {D = x ⊕ xs} (suc k) o = idOrn ⊕ updateConstructor k o
\end{code}

\begin{code}
addParameterArg : ∀{I Γ #c}{D : DatDesc I Γ #c} → Fin #c → String →
                DefOrn I id (Γ ▷₁′ Set) pop D
addParameterArg k str = updateConstructor k (str / top +⊗ idOrn)
\end{code}

\begin{code}
conRenameArguments : ∀{I Γ}{D : ConDesc I Γ} → Vec (Maybe String) (countArguments D) → Orn id id D
conRenameArguments {D = ι o} [] = ι (inv ∘ o)
conRenameArguments {D = nm / S ⊗ xs} (nm′ ∷ nms) = maybe nm id nm′ /-⊗ (conRenameArguments nms)
conRenameArguments {D = nm /rec i ⊗ xs} (nm′ ∷ nms) = maybe nm id nm′ /rec (inv ∘ i) ⊗ conRenameArguments nms
\end{code}

\begin{code}
renameArguments : ∀{I Γ #c}{D : DatDesc I Γ #c}(k : Fin #c) →
                  Vec (Maybe String) (countArguments (lookupCtor D k)) → Orn id id D
renameArguments k nms = updateConstructor k (conRenameArguments nms)
\end{code}

\section{Discussion}

