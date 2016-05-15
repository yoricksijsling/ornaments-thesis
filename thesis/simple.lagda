%include thesis.fmt

\chapter{Ornaments on dependently typed descriptions}\label{sec:simple}

The sum-of-products descriptions of Section \ref{sec:sop} can
be extended to support dependent types. In the |_⊗_| constructor we
used a |Set| to indicate which type that argument has. We want to
allow this |Set| to be determined using a local context. Arguments are
thus encoded as a function from the values in the context (|γ|) to a
|Set|. The descriptions of lists, which does not make use of the
context, now looks like this:

\begin{code}
listDesc : (A : Set) → DatDesc 2
listDesc A = ι ⊕ ((λ γ → A) ⊗ rec-⊗ ι) ⊕ `0
\end{code}

Encoding |AnyFin|, has one constructor of type |(n : Nat) → Fin n →
AnyFin|. |top γ| returns the value on top of the context, the type of
that value is determined by the |(λ γ → Nat)| of the argument before
it.

\begin{code}
anyFin : DatDesc 1
anyFin = (λ γ → Nat) ⊗ (λ γ → Fin (top γ)) ⊗ ι ⊕ `0
\end{code}

\section{Contexts}

Types in the context |Γ|, values in the context |γ|.

(Listing \ref{lst:simple-cx})
\begin{codelst}{Cx definition and semantics}{simple-cx}\begin{code}
record _▶_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pop : A
    top : B pop

mutual
  data Cx : Set₁ where
    _▷_ : (Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set) → Cx
    ε : Cx

  ⟦_⟧Cx : Cx → Set
  ⟦ Γ ▷ S ⟧Cx = ⟦ Γ ⟧Cx ▶ S
  ⟦ ε ⟧Cx = ⊤′
\end{code}\end{codelst}

\begin{code}
_▷′_ : (Γ : Cx) → Set → Cx
Γ ▷′ S = Γ ▷ const S
\end{code}

\begin{code}
example-Γ : Cx
example-Γ = ε ▷′ Set ▷′ Nat ▷ (λ γ → Vec (top (pop γ)) (top γ))

example-γ : ⟦ example-Γ ⟧Cx
example-γ = ((tt , String) , 3) , "test" ∷ "1" ∷ "2" ∷ []
\end{code}

\section{Descriptions}

Each constructor starts with an empty context |ε|. The context is then
chained through the arguments of the constructor from left to
right. In the tail of |_⊗_|, the context is extended with the value
which was specified to the left of the |_⊗_| constructor. Ideally, we
would also add recursive arguments to the context, but this is not
possible with our current implementation \todo{discuss why}.
(Listing \ref{lst:simple-desc})

\begin{codelst}{Descriptions with contexts}{simple-desc}\begin{code}
data ConDesc : Cx₁ → Set₁ where
  ι : ∀{Γ} → ConDesc Γ
  _⊗_ : ∀{Γ}(S : (γ : ⟦ Γ ⟧) → Set) → (xs : ConDesc (Γ ▷ S)) → ConDesc Γ
  rec-⊗_ : ∀{Γ}(xs : ConDesc Γ) → ConDesc Γ

data DatDesc : Nat → Set₁ where
  `0 : DatDesc 0
  _⊕_ : ∀{#c}(x : ConDesc ε)(xs : DatDesc #c) → DatDesc (suc #c)
\end{code}\end{codelst}

The semantics of |ConDesc| now needs the values in the context before
it can deliver the pattern functor.

\begin{code}
⟦_⟧conDesc : ∀{Γ} → ConDesc Γ → ⟦ Γ ⟧ → Set → Set
⟦ ι ⟧conDesc γ X = ⊤
⟦ S ⊗ xs ⟧conDesc γ X = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X
⟦ rec-⊗ xs ⟧conDesc γ X = X × ⟦ xs ⟧conDesc γ X
\end{code}

The semantics of |DatDesc| is only changed slightly to pass the value
of the empty context |tt| to |⟦_⟧conDesc|.

Dependent pairs example:

\begin{code}
pairDesc : (A : Set) (B : A → Set) → DatDesc 1
pairDesc A B = ((λ γ → A) ⊗ (λ γ → B (top γ)) ⊗ ι) ⊕ `0

pair-to : {A : Set}{B : A → Set} → Σ A B → μ (pairDesc A B)
pair-to (x , y) = ⟨ 0 , x , y , tt ⟩
\end{code}


Type of |conDescMap| is slightly different. Implementation of both
maps is the same.

\begin{code}
conDescmap : ∀{Γ X Y} (f : X → Y) (D : ConDesc Γ) →
             ∀{γ} → (v : ⟦ D ⟧ γ X) → ⟦ D ⟧ γ Y
\end{code}

Algebras for constructors can use the context.

\begin{code}
ConAlg : ∀{Γ} → ConDesc Γ → ⟦ Γ ⟧ → Set → Set
ConAlg D γ X = ⟦ D ⟧ γ X → X
\end{code}

Fold is exactly the same.

(Example of a fold that is only possible with dependent types?)

\section{Ornaments}

\begin{code}
Cxf : (Γ Δ : Cx) → Set
Cxf Γ Δ = ⟦ Γ ⟧ → ⟦ Δ ⟧
\end{code}

\begin{codelst}{Ornaments with contexts}{simple-ornament}\begin{code}
data ConOrn : ∀{Γ Δ} (f : Cxf Δ Γ) (D : ConDesc Γ) → Set₂ where
  ι : ∀{Γ Δ}{c : Cxf Δ Γ} → ConOrn c ι
  -⊗_ : ∀{Γ Δ S xs}{c : Cxf Δ Γ} → (xs⁺ : ConOrn (cxf-both c) xs) → ConOrn c (S ⊗ xs)
  rec-⊗_ : ∀{Γ Δ xs}{c : Cxf Δ Γ} → (xs⁺ : ConOrn c xs) → ConOrn c (rec-⊗ xs)

  _+⊗_ : ∀{Γ Δ xs}{c : Cxf Δ Γ} →
             (S : (δ : ⟦ Δ ⟧) → Set) → (xs⁺ : ConOrn (cxf-forget c S) xs) → ConOrn c xs
  rec-+⊗_ : ∀{Γ Δ xs}{c : Cxf Δ Γ} → (xs⁺ : ConOrn c xs) → ConOrn c xs

  give-K : ∀{Γ Δ S xs}{c : Cxf Δ Γ} →
           (s : (γ : ⟦ Δ ⟧) → S (c γ)) → (xs⁺ : ConOrn (cxf-instantiate c s) xs) → ConOrn c (S ⊗ xs)

data DatOrn : ∀{#c}(D : DatDesc #c) → Set₂ where
  `0 : DatOrn `0
  _⊕_ : ∀{#c x xs} → (x⁺ : ConOrn id x) (xs⁺ : DatOrn xs) → DatOrn {suc #c} (x ⊕ xs)
\end{code}\end{codelst}

\begin{code}
cxf-both : ∀{Γ Δ S} → (f : Cxf Δ Γ) → Cxf (Δ ▷ (S ∘ f)) (Γ ▷ S)
cxf-both f δ = f (pop δ) , top δ

cxf-forget : ∀{Γ Δ} → (f : Cxf Δ Γ) → (S : ⟦ Δ ⟧ → Set) → Cxf (Δ ▷ S) Γ
cxf-forget f S δ = f (pop δ)

cxf-instantiate : ∀{Γ Δ S} → (f : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → S (f γ)) → Cxf Δ (Γ ▷ S)
cxf-instantiate f s δ = f δ , s δ
\end{code}

Semantics of ornaments barely changes, only |-⊗_| is different.

\begin{code}
conOrnToDesc : ∀{Γ Δ}{c : Cxf Δ Γ}{D : ConDesc Γ} → ConOrn c D → ConDesc Δ
\end{code}

\begin{code}
conOrnToDesc (-⊗_ {S = S} {c = c} xs⁺) = S ∘ c ⊗ conOrnToDesc xs⁺
\end{code}

\begin{code}
conForgetNT : ∀{Γ Δ}{c : Cxf Δ Γ}{D : ConDesc Γ} (o : ConOrn c D) →
              ∀{δ X} → ⟦ o ⟧ δ X → ⟦ D ⟧ (c δ) X
\end{code}


\section{Discussion}

\begin{itemize}
\item Compare with Σdescs: Σ can also support dependent types, but
  with a Σ constructor the description of the tail is given as a
  result of a function. Stuff like |countArguments| is not
  possible. We have essentially taken the things which allow Σdescs to
  support dependent types and moved those inside the contexts.
\end{itemize}
