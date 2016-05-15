%include thesis.fmt

\chapter{Sum of products}\label{sec:sop}

In this section we give a quick introduction to generics in functional
programming using the \emph{sum-of-products} approach. We
introduce a simple universe of descriptions which can represent some
recursive datatypes. A semantics for it is given which interprets a
description to a |Set|.

\section{Descriptions}


\begin{codelst}{Sum-of-products descriptions}{sop-descriptions}\begin{code}
data ConDesc : Set₁ where
  ι : ConDesc
  _⊗_ : (S : Set) → (xs : ConDesc) → ConDesc
  rec-⊗_ : (xs : ConDesc) → ConDesc

data DatDesc : Nat → Set₁ where
  `0 : DatDesc 0
  _⊕_ : ∀{#c} (x : ConDesc) (xs : DatDesc #c) → DatDesc (suc #c)
\end{code}\end{codelst}

\begin{code}
natDesc : DatDesc 2
natDesc = ι ⊕ (rec-⊗ ι) ⊕ `0

listDesc : (A : Set) → DatDesc 2
listDesc A = ι ⊕ (A ⊗ rec-⊗ ι) ⊕ `0
\end{code}

\begin{codelst}{Sum-of-products semantics}{sop-semantics}\begin{code}
⟦_⟧conDesc : ConDesc → Set → Set
⟦ ι ⟧conDesc X = ⊤
⟦ S ⊗ D ⟧conDesc X = S × ⟦ D ⟧conDesc X
⟦ rec-⊗ D ⟧conDesc X = X × ⟦ D ⟧conDesc X

lookupCtor : ∀{#c}(D : DatDesc #c) → Fin #c → ConDesc
lookupCtor `0 ()
lookupCtor (x ⊕ _) zero = x
lookupCtor (_ ⊕ xs) (suc k) = lookupCtor xs k

⟦_⟧datDesc : ∀{#c} → DatDesc #c → Set → Set
⟦_⟧datDesc {#c} D X = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc X

data μ {#c : Nat}(F : DatDesc #c) : Set where
  ⟨_⟩ : ⟦ F ⟧datDesc (μ F) → μ F
\end{code}\end{codelst}

\begin{code}
nat-3 : μ natDesc
nat-3 = ⟨ 1 , ⟨ 1 , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩

nat-zero : μ natDesc
nat-zero = ⟨ 0 , tt ⟩
nat-suc : μ natDesc → μ natDesc
nat-suc n = ⟨ 1 , n , tt ⟩

list-nil : ∀{A} → μ (listDesc A)
list-nil = ⟨ 0 , tt ⟩
list-cons : ∀{A} → A → μ (listDesc A) → μ (listDesc A)
list-cons x xs = ⟨ 1 , x , xs , tt ⟩
\end{code}


\section{Maps and folds}

Map over the pattern functor
\begin{codelst}{Generic map}{sop-map}\begin{code}
conDescmap : ∀{X Y} (f : X → Y) (D : ConDesc) →
             (v : ⟦ D ⟧ X) → ⟦ D ⟧ Y
conDescmap f ι tt = tt
conDescmap f (S ⊗ xs) (s , v) = s , conDescmap f xs v
conDescmap f (rec-⊗ xs) (s , v) = f s , conDescmap f xs v

datDescmap : ∀{#c X Y} (f : X → Y) (D : DatDesc #c) →
             (v : ⟦ D ⟧ X) → ⟦ D ⟧ Y
datDescmap f xs (k , v) = k , conDescmap f (lookupCtor xs k) v
\end{code}\end{codelst}

\begin{code}
DatAlg : ∀{#c} → DatDesc #c → Set → Set
DatAlg D X = ⟦ D ⟧ X → X
ConAlg : ConDesc → Set → Set
ConAlg D X = ⟦ D ⟧ X → X
\end{code}

\begin{code}
fold : ∀{#c}{D : DatDesc #c}{X} (α : DatAlg D X) → μ D → X
fold {D = D} α ⟨ xs ⟩ = α (datDescmap (fold α) D xs)
\end{code}

Example, sum algebra for lists of naturals:

\begin{code}
sumAlg : DatAlg (listDesc Nat) Nat
sumAlg (zero , tt) = 0
sumAlg (suc zero , x , xs , tt) = x + xs
sumAlg (suc (suc ()) , _)
\end{code}


\section{Ornaments}

\begin{codelst}{Definition of ornaments}{sop-ornaments}\begin{code}
infixr 4 -⊗_ _+⊗_ rec-+⊗_
data ConOrn : (D : ConDesc) → Set₁ where
  ι : ConOrn ι
  -⊗_ : ∀{S xs} → (xs⁺ : ConOrn xs) → ConOrn (S ⊗ xs)
  rec-⊗_ : ∀{xs} → (xs⁺ : ConOrn xs) → ConOrn (rec-⊗ xs)

  _+⊗_ : ∀{xs}(S : Set) → (xs⁺ : ConOrn xs) → ConOrn xs
  rec-+⊗_ : ∀{xs} → (xs⁺ : ConOrn xs) → ConOrn xs

  give-K : ∀{S xs} (s : S) → (xs⁺ : ConOrn xs) → ConOrn (S ⊗ xs)

data DatOrn : ∀{#c}(D : DatDesc #c) → Set₂ where
  `0 : DatOrn `0
  _⊕_ : ∀{#c x xs} → (x⁺ : ConOrn x) (xs⁺ : DatOrn xs) → DatOrn {suc #c} (x ⊕ xs)
\end{code}\end{codelst}

Ornaments have a semantics which results in a description:

\begin{code}
conOrnToDesc : ∀{D} → ConOrn D → ConDesc
conOrnToDesc ι = ι
conOrnToDesc (-⊗_ {S = S} xs⁺) = S ⊗ conOrnToDesc xs⁺
conOrnToDesc (rec-⊗ xs⁺) = rec-⊗ conOrnToDesc xs⁺
conOrnToDesc (S +⊗ xs⁺) = S ⊗ conOrnToDesc xs⁺
conOrnToDesc (rec-+⊗ xs⁺) = rec-⊗ conOrnToDesc xs⁺
conOrnToDesc (give-K s xs⁺) = conOrnToDesc xs⁺
ornToDesc : ∀{#c}{D : DatDesc #c} → DatOrn D → DatDesc #c
ornToDesc `0 = `0
ornToDesc (x⁺ ⊕ xs⁺) = conOrnToDesc x⁺ ⊕ ornToDesc xs⁺
\end{code}

Example:
\begin{code}
nat→stringlist : DatOrn natDesc
nat→stringlist = ι ⊕ (String +⊗ rec-⊗ ι) ⊕ `0

test-nat→stringlist : ornToDesc nat→stringlist ≡ listDesc String
test-nat→stringlist = refl
\end{code}

\section{Ornamental algebras}

\begin{code}
conForgetNT : ∀{D} (o : ConOrn D) →
              ∀{X} → ⟦ o ⟧ X → ⟦ D ⟧ X
conForgetNT ι tt = tt
conForgetNT (-⊗ xs⁺) (s , v) = s , conForgetNT xs⁺ v
conForgetNT (rec-⊗ xs⁺) (s , v) = s , conForgetNT xs⁺ v
conForgetNT (_+⊗_ S xs⁺) (s , v) = conForgetNT xs⁺ v
conForgetNT (rec-+⊗_ xs⁺) (s , v) = conForgetNT xs⁺ v
conForgetNT (give-K s xs⁺) v = s , conForgetNT xs⁺ v

forgetNT : ∀{#c}{D : DatDesc #c} (o : DatOrn D) → ∀{X} → ⟦ o ⟧ X → ⟦ D ⟧ X
forgetNT `0 (() , _)
forgetNT (x⁺ ⊕ xs⁺) (zero , v) = 0 , conForgetNT x⁺ v
forgetNT (x⁺ ⊕ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

forgetAlg : ∀{#c}{D : DatDesc #c} (o : DatOrn D) → DatAlg (ornToDesc o) (μ D)
forgetAlg o = ⟨_⟩ ∘ forgetNT o

forget : ∀{#c}{D : DatDesc #c} (o : DatOrn D) → μ (ornToDesc o) → μ D
forget o = fold (forgetAlg o)
\end{code}

Example, length of lists:

\begin{code}
ex-list : μ (listDesc String)
ex-list = ⟨ 1 , "Test" , ⟨ 1 , "one" , ⟨ 1 , "two" , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩ , tt ⟩

forget-list : forget nat→stringlist ex-list ≡ ⟨ 1 , ⟨ 1 , ⟨ 1 , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩ , tt ⟩
forget-list = refl
\end{code}

\section{Discussion}

\begin{itemize}
\item Why is the Dat/Con split useful
\item Choice of ornaments: Every ornament must give rise to an
  ornamental algebra. Ornaments can be interpreted as refinements
  (?). All of our ornaments can be derived from those in 'transporting
  functions', even though they use Σdescs. We do not have a
  'reconstructor' ornament which does insert/give on the top-level.
\end{itemize}