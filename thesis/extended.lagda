%include thesis.fmt

\chapter{Ornaments on families of datatypes}\label{chap:extended}

Datatype parameters and indices will be added to our descriptions in
this chapter. They form the final components to be able to describe a
large portion of Agda datatypes. Ornaments will again be updated to
work with these descriptions. The addition of indices allows the
implementation of some of the surrounding theory around ornaments.

Parameters are a natural extension of contexts within
descriptions---the only difference is that a full type does not need
to be closed. Where we previously always started with an empty context
|ε| for each constructor, now the whole datatype description can have
a context. Within the constructors, the parameters are available as
variables in the environment and they can be used with |top| and
|pop|. Though the contexts are specified during the definition of a
description, the transformation of a description into a |Set| requires
the user to pass an environment containing the parameters. This is
similar to how the parameters of an Agda datatype have to be
instantiated before you get a |Set|.

Indices are added to our descriptions as well. When indices are used,
we are not just describing a single type but a family of types. A
recursive call within a type can refer to any of the family members,
so in every |rec_⊗_| we must specify an index to pick a type within
the family. Additionally, every type must tell us which index it
has. This is done by requiring an index to be specified in the |ι|
constructor as well. The way we implement indices is a lot like
McBride's approach \cite{mcbride11}, though we make use of our |Cx|
datatype to allow multiple indices.

Parameters and indices will both be declared using a |Cx| as a
parameter on the |DatDesc| type. A type like |Vec|, which has one
parameter of type |Set| and one index of type |Nat|, is described with
the type |DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2|.

\section{Descriptions}

Descriptions of constructors where already parametrised by a |(Γ :
Cx₁)|, now we also add a parameter |(I : Cx₀)|. Descriptions for
datatypes are parametrised by |(Γ : Cx₁)| and |(I : Cx₀)| as well. The
indices |I| stay constant across all constructors. The context |Γ| is
initially equal to the parameters, but can be extended within the
constructors like in the previous chapter.

\Fref{lst:ext-desc} shows the new definitions for |ConDesc|
and |DatDesc|. The interesting changes are in the |ι| and |rec_⊗_|
constructors, which both have gained a new argument. In the |ι|
constructor, the user must tell us an index of type |⟦ I ⟧|. They are
allowed to use the local environment |(γ : ⟦ Γ ⟧)|. The |rec_⊗_|
constructor also requires the specification of an index of type |⟦ I
⟧|, and here too the local environment can be used.

\begin{codelst}{Descriptions of families of datatypes}{ext-desc}\begin{code}
data ConDesc (I : Cx₀)(Γ : Cx₁) : Set₁ where
  ι : (o : (γ : ⟦ Γ ⟧) → ⟦ I ⟧) → ConDesc I Γ
  _⊗_ : (S : (γ : ⟦ Γ ⟧) → Set) → (xs : ConDesc I (Γ ▷ S)) → ConDesc I Γ
  rec_⊗_ : (i : (γ : ⟦ Γ ⟧) → ⟦ I ⟧) → (xs : ConDesc I Γ) → ConDesc I Γ
data DatDesc (I : Cx)(Γ : Cx) : (#c : Nat) → Set₁ where
  `0 : DatDesc I Γ 0
  _⊕_ : ∀{#c}(x : ConDesc I Γ)(xs : DatDesc I Γ #c) →
    DatDesc I Γ (suc #c)
\end{code}\end{codelst}

Before the semantics for |ConDesc| and |DatDesc| are defined, we will
take a slight detour. In previous chapters many functions for
|ConDesc| and |DatDesc| were defined separately. Now that |ConDesc|
and |DatDesc| have some overlapping parameters, it will become
bothersome to have to write many of the same function signatures for
both of them. This is circumvented by defining a small universe in
\fref{lst:ext-desctag}. Using |DescTag| and |Desc|, we can refer to
|ConDesc I Γ| as |Desc I Γ isCon| and to |DatDesc I Γ #c| as |Desc I Γ
(isDat #c)|. Functions which have to be defined on both |ConDesc| and
|DatDesc| can now be defined on |Desc dt| for all |dt|.

\begin{codelst}{Definition of |DescTag| and |Desc|}{ext-desctag}\begin{code}
data DescTag : Set₂ where
  isCon : DescTag
  isDat : (#c : Nat) → DescTag

Desc : (I : Cx) → (Γ : Cx) → DescTag → Set₁
Desc I Γ (isCon) = ConDesc I Γ
Desc I Γ (isDat #c) = DatDesc I Γ #c
\end{code}\end{codelst}

The semantics of descriptions is one of those functions which have the
same type for both |ConDesc| and |DatDesc|. The type is quantified
over all |dt|, so it takes the following form:

\begin{code}
⟦_⟧desc : ∀{I Γ dt} → Desc I Γ dt → ?
\end{code}

The type which goes in the hole |?| is a bit more involved than what
we have previously seen. The semantics of |DatDesc| in the previous
chapters gave an endofunctor on |Set|. Dybjer \cite{dybjer94} has
shown how an inductive family (with indices) can be described using an
endofunctor on |I′ → Set|. We use |⟦ I ⟧| instead of |I′|, to encode
the idea of having a telescope of indices instead of just one. By
interpreting the description as an endofunctor on |⟦ I ⟧ → Set|, the
recursive positions are allowed to pick an index of type |⟦ I ⟧| in
return for a |Set|. An environment for the current context has to be
passed in as well, but this is not part of the functor. This results
in the following type:

\begin{code}
⟦_⟧desc : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → (⟦ I ⟧ → Set) → (⟦ I ⟧ → Set)
\end{code}

The full definition of |⟦_⟧desc| is given in
\fref{lst:ext-semantics}. In every clause, we get a local environment
|γ| just like we did in |⟦_⟧conDesc| in
\fref{sec:simple-descriptions}---this time including the
parameters. The value |X| of type |⟦ I ⟧ → Set| is used in the clause
for |rec i ⊗ xs| to pick one of the members of the inductive
family. The |o| is what we are being told what the index of the type
\emph{should} be. In |ι o′|, the description \emph{says} that the
index is |o′ γ|. Therefore, the interpretation of |ι o′| is an equality
constraint |o′ γ ≡ o|. The use of the indices is similar to McBride's
definitions \cite{mcbride11}, but here the indices are determined with
help of the local environment |γ|.

\begin{codelst}{Semantics of datatype families}{ext-semantics}\begin{code}
⟦_⟧desc : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → (⟦ I ⟧ → Set) → (⟦ I ⟧ → Set)
⟦_⟧desc {dt = isCon} (ι o′) γ X o = o′ γ ≡ o
⟦_⟧desc {dt = isCon} (S ⊗ xs) γ X o = Σ (S γ) λ s → ⟦ xs ⟧desc (γ , s) X o
⟦_⟧desc {dt = isCon} (rec i ⊗ xs) γ X o = X (i γ) × ⟦ xs ⟧desc γ X o
⟦_⟧desc {dt = isDat #c} D γ X o = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧desc γ X o

data μ {I Γ #c} (D : DatDesc I Γ #c) (γ : ⟦ Γ ⟧) (o : ⟦ I ⟧) : Set where
  ⟨_⟩ : ⟦ D ⟧ γ (μ D γ) o → μ F γ o
\end{code}\end{codelst}

By partially applying the fixpoint datatype |μ| with a description |D|
and the parameters |γ|, we get |μ D γ| of type |⟦ I ⟧ → Set|. This is
exactly the type we need to pass to |⟦_⟧desc| within the definition of
the |⟨_⟩| constructor. The parameters, i.e. the starting environment,
are passed along unchanged to all the recursive children.

\begin{example}
The |List| type has no indices and one parameter of type |Set|, so the
description is of type |DatDesc ε (ε ▷₁′ Set) 2|. The |ι| and |rec_⊗_|
constructors both require the user to specify an index---this can only
be |tt| as that is the only inhabitant of |⟦ ε ⟧|. The description of
|List| can now be defined as follows:

\begin{code}
listDesc : DatDesc ε (ε ▷₁′ Set) 2
listDesc = ι (const tt) ⊕
  top ⊗ rec (const tt) ⊗ ι (const tt) ⊕
  `0
\end{code}

Comparing this to how |listDesc| was defined in
\fref{sec:sop-descriptions} and the introduction of
\fref{chap:simple}, we see that the use of the parameter has been
internalised. Where it used to say |A|, we now see a |top|.

The fixpoint of descriptions is aware of parameters and indices, and
it is required to instantiate them before we obtain a |Set|. The type
of |μ listDesc| is now |⟦ ε ▷₁′ Set ⟧ →| |⟦ ε ⟧ → Set|. Ignoring the
fluff, one can see how this is similar to the type of |List|: |Set →
Set|. The function |list-to| shows how |μ listD| can be used:

\begin{code}
list-to : ∀{A} → List A → μ listD (tt , A) tt
list-to [] = ⟨ 0 , refl ⟩
list-to (x ∷ xs) = ⟨ 1 , x , list-to xs , refl ⟩
\end{code}

With the descriptions of \fref{chap:sop} and \fref{chap:simple}, the
type of |list-to| would have been |∀{A} → List A → μ (listDesc A)|.
\end{example}

\begin{example}
One of the simplest inductive families we can make is those of finite
naturals. It has the normal |zero| and |suc| constructors of naturals,
but it is indexed by a |Nat| which limits how high the value can
be. The set |Fin n| contains naturals which are lower than |n|. It is
usually defined as follows:

\begin{code}
data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} (i : Fin n) → Fin (suc n)
\end{code}

The |Fin| type can be described by a |DatDesc (ε ▷′ Nat) ε|. Our
descriptions do not allow implicit arguments, so we make them
explicit. We can easily write down part of the description, leaving
open the holes where all the indices have to be specified:

\begin{code}
finDesc : DatDesc (ε ▷′ Nat) ε 2
finDesc = const Nat ⊗ ι ?1
  ⊕ const Nat ⊗ rec ?2 ⊗ ι ?3
  ⊕ `0
\end{code}

All the open holes happen to have a local context where just one |Nat|
exists, so they all require a term of type |⟦ ε ▷′ Nat ⟧ → ⟦ ε ▷′ Nat
⟧|. This situation is comparable to what we would get if we defined
|Fin| using one parameter of type |⟦ ε ⟧| and one index of type |⟦ ε
▷′ Nat ⟧|. In the following definition all the holes have |(A : ⟦ ε
⟧)| and |(n : Nat)| in the context, and have to be of type |⟦ ε ▷′ Nat
⟧|.

\begin{code}
data FinTT (A : ⟦ ε ⟧) : ⟦ ε ▷′ Nat ⟧ → Set where
  zero : (n : Nat) → FinTT A ?1
  suc : (n : Nat) (i : FinTT A ?2) → FinTT A ?3
\end{code}

The definition of |FinTT| could be completed by filling in |(tt , suc
n)|, |(tt , n)| and |(tt , suc n)| in the holes. To complete the
definition of |finDesc|, we have to consider how the environment is
passed around as well. We use the combinator |_<,>_|, as defined in
\fref{lst:ext-envpair}, to spread the environment over its
arguments:

\begin{codelst}{Definition of |_<,>_|}{ext-envpair}\begin{code}
_<,>_ : ∀ {a b c} → {Γ : Set c}{A : Set a}{B : A → Set b} →
        (f : (γ : Γ) → A) → (g : (γ : Γ) → B (f γ)) → (γ : Γ) → A ▶ B
f <,> g = _,_ <KS> f <S> g
\end{code}\end{codelst}

\begin{code}
finDesc : DatDesc (ε ▷′ Nat) ε 2
finDesc = const Nat ⊗ ι (const tt <,> suc <KS> top)
  ⊕ const Nat ⊗ rec (const tt <,> top) ⊗ ι (const tt <,> suc <KS> top)
  ⊕ `0
\end{code}

An element of type |μ finDesc tt (tt , 10)| is a natural which is
lower than 10. Let us build such an element which represents the value
zero. This is done by immediately picking the first constructor (|⟨ 0
, ... ⟩|). Then we need to give a |Nat|, which is the implicit |n| in
the definition of |Fin|, and a proof that the created element has the
right index.

\begin{code}
fin-zero′ : μ finDesc tt (tt , 10)
fin-zero′ = ⟨ 0 , ?0 , ?1 ⟩
-- |?0| : Nat
-- |?1| : (tt , suc ?0) ≡ (tt , 10)
\end{code}

The obvious definitions for the holes |?0| and |?1| are |9| and
|refl|, completing the definition of |fin-zero|.

\begin{code}
fin-zero : μ finDesc tt (tt , 10)
fin-zero = ⟨ 0 , 9 , refl ⟩
\end{code}
\end{example}

We claimed that |⟦_⟧desc| gave us a functor on |⟦ I ⟧ → Set|, so we
should be able to define a functorial map. Within functional
programming, we often assume that functors are from the |Set| category
to the |Set| category, with functions as the arrows. When working in
the |⟦ I ⟧ → Set| category, one has to reconsider what the arrows
are. The arrows are characterised as functions which respect indexing,
they are defined as |_→ⁱ_| in
\fref{lst:ext-indexedarrows}\footnote{Actually, the |_→ⁱ_| definition
  works for the more general category |I → Set|, of which |⟦ I ⟧ →
  Set| is an instance.}.

\begin{codelst}{Arrows in the |I → Set| category}{ext-indexedarrows}\begin{code}
_→ⁱ_ : {I : Set} → (I → Set) → (I → Set) → Set
X →ⁱ Y = ∀{i} → X i → Y i
\end{code}\end{codelst}

A map function for a functor |F| in the |I → Set| category should lift
an arrow |X →ⁱ Y| to an arrow |F X →ⁱ F Y|. By choosing |⟦ D ⟧ γ| as
|F| we get the type for |descmap|, which is fully defined in
\fref{lst:ext-map}. The implementation is straightforward, but it is
listed for completeness. 

\begin{codelst}{Map for pattern functors with indices}{ext-map}\begin{code}
descmap : ∀{I Γ dt X Y} (f : X →ⁱ Y) (D : Desc I Γ dt) →
  ∀{γ} → ⟦ D ⟧ γ X →ⁱ ⟦ D ⟧ γ Y
descmap {dt = isCon} f (ι o) refl = refl
descmap {dt = isCon} f (S ⊗ xs) (s , v) = s , descmap f xs v
descmap {dt = isCon} f (rec i ⊗ xs) (s , v) = f s , descmap f xs v
descmap {dt = isDat _} f xs (k , v) = k , descmap f (lookupCtor xs k) v
\end{code}\end{codelst}

The definitions of the |Alg| and |fold| in \fref{lst:ext-fold} are
lifted to the |⟦ I ⟧ → Set| category in a similar way, by replacing
some of the arrows |_→_| with |_→ⁱ_|. An environment |⟦ Γ ⟧| has to be
passed to |Alg|, because an algebra may only work for a specific
environment. For example; an algebra to calculate the sum of a list
would be of type |Alg listDesc (tt , Nat) (const Nat)|, where the
|Nat| is passed in the environment to instantiate the parameter. Other
algebras like the one to calculate the length will work for any
parameter, so it will have the type |∀{A} → Alg listDesc (tt , A)
(const Nat)|. The code below demonstrates how these algebras can be
defined:

\begin{codelst}{Generic fold}{ext-fold}\begin{code}
Alg : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → (⟦ I ⟧ → Set) → Set
Alg {I} D γ X = ⟦ D ⟧ γ X →ⁱ X

fold : ∀{I Γ #c}{D : DatDesc I Γ #c}{γ X} (α : Alg D γ X) → μ D γ →ⁱ X
fold {D = D} α ⟨ xs ⟩ = α (descmap (fold α) D xs)
\end{code}\end{codelst}

\begin{code}
sumAlg : Alg listDesc (tt , Nat) (const Nat)
sumAlg (zero , refl) = 0
sumAlg (suc zero , x , xs , refl) = x + xs
sumAlg (suc (suc ()) , _)

lengthAlg : ∀{A} → Alg listDesc (tt , A) (const Nat)
lengthAlg (zero , refl) = 0
lengthAlg (suc zero , x , xs , refl) = suc xs
lengthAlg (suc (suc ()) , _)
\end{code}

\begin{example}
An algebra can be used to define the |raise| function for |Fin|. It
takes a natural |m| and lifts a |Fin n| into |Fin (n + m)| while the
represented value stays the same. It has the following type:

\begin{code}
raise : ∀{n} → (m : Nat) → Fin n → Fin (n + m)
\end{code}

An algebra on |finDesc| which calculates this value should have |μ
finDesc tt (tt ,| |n + m)| as its return type, where |n| is the index of
the |Fin| which was given. This can be represented using the |⟦ I ⟧ →
Set| function which is required by |Alg|. To refer to |n| we take the
|top| of the indices, giving us the following type for |raiseAlg|:

\begin{code}
raiseAlg : (m : Nat) → Alg finDesc tt (λ i → μ finDesc tt (tt , top i + m))
\end{code}

The rest of the definition is a straightforward case split on the
constructors. In the pattern for zero we build a new zero, and in the
pattern for suc we build a new suc. In both cases the index changes
from |n| to |n + m|.

\begin{code}
raiseAlg : (m : Nat) → Alg finDesc tt (λ i → μ finDesc tt (tt , top i + m))
raiseAlg m (zero , n , refl) = ⟨ 0 , n + m , refl ⟩
raiseAlg m (suc zero , n , k , refl) = ⟨ 1 , n + m , k , refl ⟩
raiseAlg m (suc (suc ()) , _)
\end{code}

To complete the definition of |raise|, we use the embedding-projection
pair as defined below with |fin-to| and |fin-from|. The |raise|
function converts a real |Fin| to a |μ finDesc|, folds |raiseAlg m|
over it, and converts it back to a |Fin|.

\begin{code}
fin-to : ∀{n} → Fin n → μ finDesc tt (tt , n)
fin-to zero = ⟨ 0 , _ , refl ⟩
fin-to (suc k) = ⟨ 1 , _ , fin-to k , refl ⟩

fin-from : ∀{n} → μ finDesc tt (tt , n) → Fin n
fin-from ⟨ zero , _ , refl ⟩ = zero
fin-from ⟨ suc zero , _ , k , refl ⟩ = suc (fin-from k)
fin-from ⟨ suc (suc ()) , _ ⟩

raise : ∀{n} → (m : Nat) → Fin n → Fin (n + m) 
raise m = fin-from ∘ fold (raiseAlg m) ∘ fin-to
\end{code}

The |raise| function is verified by creating a |Fin 5| with the value
2 and raising it with 4. The result is a |Fin 9| with the value 2, as
expected.

\begin{code}
f2<5 : Fin 5
f2<5 = suc (suc zero)

f2<9 : Fin 9
f2<9 = raise 4 f2<5

check-f2<9 : f2<9 ≡ suc (suc zero)
check-f2<9 = refl
\end{code}
\end{example}


\section{Ornaments}\label{sec:ext-ornaments}

The definition of ornaments on descriptions with parameters and
indices is mostly based on the constructor ornaments of
\fref{sec:simple-ornaments} (\fref{lst:simple-ornament}). The same
context transformers (\fref{lst:simple-cxf}) are used, but this time
on both the indices and the context/parameters. Many of the parts
relating to indices are based on McBride's ornaments \cite{mcbride11}.

Using our |DescTag| codes, a single datatype for ornaments can be
defined which contains ornaments for both |ConDesc| and
|DatDesc|. Like |ConOrn| of \fref{sec:simple-ornaments}, it contains
the starting context |Γ|, the result context |Δ| and an environment
transformer |(u : Cxf Δ Γ)| as parameters. The indices are added in a
similar way using a starting index |I|, result index |J| and a
transformer between indices |(u : Cxf J I)|. The |Orn| datatype gets
the following signature:

\begin{code}
data Orn {I} J (u : Cxf J I) {Γ} Δ (c : Cxf Δ Γ) :
  ∀{dt}(D : Desc I Γ dt) → Set₁
\end{code}

Remember that the type |Cxf J I| of the index transformer |u| expands
to |⟦ J ⟧ → ⟦ I ⟧|.  This type can be interpreted as a one-to-many
mapping from One way to interpret such a type, is that It is a mapping
from the indices of elements in the ornamented type back to indices in
the original type. It ensures that the index |J| is more informative
than |I|, and that that extra information can be forgotten. When the
origina. Like McBride, we use a datatype to define the inverse image
of a function: \todo{fix explanation of inv}.

An small module is used with for the parameters |a|, |b|, |A| and
|B|. These arguments are shared between all three functions. Because
the module is nameless (it is named |_|), the module is transparent to
function calls---Meaning that outside the module, these functions can
be called as if they had been defined there with the module parameters
as function arguments.

\begin{codelst}{Inverse image of functions}{ext-inverseimage}\begin{code}
module _ {a b}{A : Set a}{B : Set b} where
  -- |f ⁻¹ y| contains an |x| such that |f x ≡ y|
  data _⁻¹_ (f : A → B) : (y : B) → Set (a ⊔ b) where
    inv : (x : A) → f ⁻¹ (f x)

  uninv : {f : A → B}{y : B} → f ⁻¹ y → A
  uninv (inv x) = x

  inv-eq : {f : A → B}{y : B} → (x : f ⁻¹ y) → f (uninv x) ≡ y
  inv-eq (inv x) = refl
\end{code}\end{codelst}

In \fref{lst:ext-ornament} the new ornaments are defined. All the
constructors now fit in a single |Orn| datatype, and the contexts are
now propagated in the |`0| and |_⊕_| ornaments as well.  The |rec_+⊗_|
ornament gains a simple extension: an index |j| of type |⟦ J ⟧| can be
chosen by making use of the ornamented environment |δ|.

In the |ι| and |rec_⊗_| copy ornaments, a new index must be given
which---for the function |u|---lies in the inverse image of the
original index. The ornamented environment |δ| may be used to
determine this index. The orinal index |i| can only be determined
using the original environment, which is reconstructed by applying the
environment transformer |c| to the ornamented environment |δ|.

\begin{codelst}{Ornaments for families of datatypes}{ext-ornament}\begin{code}
data Orn {I} J (u : Cxf J I)
  {Γ} Δ (c : Cxf Δ Γ) : ∀{dt}(D : Desc I Γ dt) → Set₁ where
  ι : ∀{i} → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) → Orn _ u _ c (ι i)
  -⊗_ : ∀{S xs} → (xs⁺ : Orn _ u _ (cxf-both c) xs) → Orn _ u _ c (S ⊗ xs)
  rec_⊗_ : ∀{i xs} → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (c δ))) →
    (xs⁺ : Orn _ u _ c xs) → Orn _ u _ c (rec i ⊗ xs)

  _+⊗_ : ∀{xs : ConDesc I Γ} → (S : (δ : ⟦ Δ ⟧) → Set) →
    (xs⁺ : Orn _ u _ (cxf-forget c S) xs) → Orn _ u _ c xs
  rec_+⊗_ : ∀{xs : ConDesc I Γ} → (j : (δ : ⟦ Δ ⟧) → ⟦ J ⟧) →
    (xs⁺ : Orn _ u _ c xs) → Orn _ u _ c xs
  give-K : ∀{S xs} → (s : (δ : ⟦ Δ ⟧) → S (c δ)) →
    (xs⁺ : Orn _ u _ (cxf-inst c s) xs) → Orn _ u _ c (S ⊗ xs)

  `0 : Orn _ u _ c `0
  _⊕_ : ∀{#c x}{xs : DatDesc I Γ #c} →
    (x⁺ : Orn _ u _ c x) (xs⁺ : Orn _ u _ c xs) → Orn _ u _ c (x ⊕ xs)
\end{code}\end{codelst}

The semantics of ornaments is listed in \fref{lst:ext-orntodesc}. A
small nameless module is used to put the quantification over |I|, |J|
and |u| outside of the |ornToDesc| function. Module parameters in Agda
remain constant between calls within the module, so this emphasises
that the indices are the same within every part of a description.

The combination of |ConDesc| and |DatDesc| into a single |Desc| type
works very well here: A single function is required to define the
semantics of ornaments on both constructors and datatypes and there is
no mention of |DescTag|s within the clauses. The term |uninv ∘ j|
occurs twice, in the clauses for |ι j| and for |rec j ⊗ xs⁺|. The
function |j| gives the new index, of type |u ⁻¹ i (c δ)|, when it is
applied to an ornamented environment. The index is then extracted from
using |uninv|.

\begin{codelst}{Interpretation of ornaments}{ext-orntodesc}\begin{code}
module _ {I J u} where
  ornToDesc : ∀{Γ Δ c dt}{D : Desc I Γ dt} →
    (o : Orn J u Δ c D) → Desc J Δ dt
  ornToDesc (ι j) = ι (uninv ∘ j)
  ornToDesc {c = c} (-⊗_ {S = S} xs⁺) = S ∘ c ⊗ ornToDesc xs⁺
  ornToDesc (rec j ⊗ xs⁺) = rec (uninv ∘ j) ⊗ ornToDesc xs⁺
  ornToDesc (_+⊗_ S xs⁺) = S ⊗ ornToDesc xs⁺
  ornToDesc (rec_+⊗_ j xs⁺) = rec j ⊗ ornToDesc xs⁺
  ornToDesc (give-K s xs⁺) = ornToDesc xs⁺
  ornToDesc `0 = `0
  ornToDesc (x⁺ ⊕ xs⁺) = ornToDesc x⁺ ⊕ ornToDesc xs⁺
\end{code}\end{codelst}

\begin{example}
Let us get some practice with the new ornaments by refining
lists to |Vec|s. Recall the definition of the |Vec| type:

\begin{code}
data Vec (A : Set) : Nat → Set where
  [] : Vec A 0
  _∷_ : ∀{n} → (x : A) → (xs : Vec A n) → Vec A (suc n)
\end{code}

The |Vec| type has one index of type |Nat| and one
parameter of type |Set|. By using |listDesc| as the starting point,
the type of the ornament to be defined has the following structure:

\begin{code}
list→vec : Orn (ε ▷′ Nat) ?0 (ε ▷₁′ Set) ?1 listDesc
\end{code}

The hole |?0| is the index transformer and must have be of type |⟦ ε
▷′ Nat ⟧ → ⟦ ε ⟧|. The result type has only one inhabitant, so the
implementation is easily given as |λ j → tt|. The parameter
transformer |?1| must have type |⟦ ε ▷₁′ Set ⟧ → ⟦ ε ▷₁′ Set ⟧|. We do
not want the parameters to change---if |A| is the parameter for the
list, |A| should be the parameter for the |Vec|---so we use the
identity function |id|. Structurally, the ornament should only insert
one argument; the |n| in the |_∷_| constructor with which the index
is determined. Skipping the indices, the ornament looks as follows.

\begin{code}
list→vec : Orn (ε ▷′ Nat) (λ j → tt) (ε ▷₁′ Set) id listDesc
list→vec = ι ?0
  ⊕ const Nat +⊗ -⊗ rec ?1 ⊗ ι ?2
  ⊕ `0

-- |?0 : (δ : ⊤′ ▶₁ const Set) → (λ j → tt) ⁻¹ tt|
-- |?1 : (δ : ⊤′ ▶₁ const Set ▶₀ const Nat ▶₀ top ∘ pop) → (λ j → tt) ⁻¹ tt|
-- |?2 : (δ : ⊤′ ▶₁ const Set ▶₀ const Nat ▶₀ top ∘ pop) → (λ j → tt) ⁻¹ tt|
\end{code}

The first hole to be filled in asks for a |(λ j → tt) ⁻¹ tt|, this
means we can fill in |inv x| where |x| must be of type |⟦ ε ▷′ Nat ⟧|
(the type of the new indices) and |(λ j → tt) x| must be equal to
|tt|. The second requirement is met trivially, so any value with the
right type will do. In this case the length index should be zero, so
|tt , 0| is filled in.

For the holes |?1| and |?2| the situations are similar, any index of
type |⟦ ε ▷′ Nat ⟧| can be chosen. Note that both holes can use the
ornamented environment, including the new argument of type |Nat|, to
determine the index. The holes |?1| and |?2| are filled in to use |n|
and |suc n| respectively as the length index.

\begin{code}
list→vec : Orn (ε ▷′ Nat) (λ _ → tt) (ε ▷₁′ Set) id listDesc
list→vec = ι (λ δ → inv (tt , 0))
  ⊕ const Nat +⊗ -⊗ rec (λ δ → inv (tt , top (pop δ)))
  ⊗ ι (λ δ → inv (tt , suc (top (pop δ))))
  ⊕ `0
\end{code}

As a quick verification that this ornament results in a type which
does the same thing as |Vec|, part of the embedding-projection pair is
given:

\begin{code}
vecDesc : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
vecDesc = ornToDesc list→vec

vec-to : ∀{A n} → Vec A n → μ vecDesc (tt , A) (tt , n)
vec-to [] = ⟨ 0 , refl ⟩
vec-to (x ∷ xs) = ⟨ 1 , _ , x , vec-to xs , refl ⟩
\end{code}

\end{example}

The ornamental algebra is an extension of the ornamental algebras we
have seen before. The full listing is given in
\fref{lst:ext-forget}. The index types |I| and |J| and the index
transformer |u| are module parameters to emphasise that they remain
the same between |forget|, |forgetAlg| and |forgetNT|.

The type of |forgetNT| is similar to that of |conForgetNT| in
\fref{sec:simple-ornaments}, in that they go from the functor |⟦
ornToDesc o ⟧ δ| to the functor |⟦ D ⟧ (c δ)|. The \emph{ornamented}
environment is passed as an argument to |forgetNT|, and the
environment for the original type is obtained by applying the
environment transformer |c|. Both functors require a new argument
containing an index (to get to a |Set|), these are handled similarly
to the environments. The index |j| of the ornamented type is
transformed to the index for the original type by applying |u|. An |X|
of type |⟦ I ⟧ → Set| can be combined with |u| (of type |⟦ J ⟧ → ⟦ I
⟧| to get the other arguments for the functors. The resulting types
are similar to those of McBride \cite{mcbride11}, with the addition of
environments.

The cases of |forgetNT| for |ι j| and |rec j ⊗ xs⁺| both require the
proof |inv-eq (j δ)|. In both clauses |j δ| is of type |u ⁻¹ i (c δ)|,
so it contains a value in the inverse-image of |i (c δ)|. The proof
|inv-eq (j δ)| says that |u (uninv (j δ)) ≡ i (c δ)|, confirming that
applying |u| on the ornamented index (|j δ|) results in the original
index (|i (c δ)|). Alternatively, we might state: The index |j| under
the environment |δ| lies in the inverse-image for |u| of |i| under the
environment |c δ|. Rewriting with the proof unifies enough variables
that the proof obligation for the |ι j| case becomes |i (c δ) ≡ i (c
δ)|, allowing us to write |refl| as the term. The type of |s| in the
|rec j ⊗ xs⁺| case is rewritten to |X (i (c δ))|, which is exactly
what is needed on the right side.

\begin{codelst}{Ornamental algebras}{ext-forget}\begin{code}
module _ {I J u} where
  forgetNT : ∀{Γ Δ c dt}{D : Desc I Γ dt} (o : Orn J u Δ c D) →
             ∀{δ X j} → ⟦ ornToDesc o ⟧ δ (X ∘ u) j → ⟦ D ⟧ (c δ) X (u j)
  forgetNT (ι j) {δ} refl rewrite inv-eq (j δ) = refl
  forgetNT (-⊗ xs⁺) (s , v) = s , forgetNT xs⁺ v
  forgetNT (rec j ⊗ xs⁺) {δ} {X} (s , v) rewrite inv-eq (j δ) = s , forgetNT xs⁺ v
  forgetNT (_+⊗_ S xs⁺) (s , v) = forgetNT xs⁺ v
  forgetNT (rec_+⊗_ j xs⁺) (s , v) = forgetNT xs⁺ v
  forgetNT (give-K s xs⁺) {δ} v = s δ , forgetNT xs⁺ v
  forgetNT `0 (() , _)
  forgetNT (x⁺ ⊕ xs⁺) (zero , v) = zero , forgetNT x⁺ v
  forgetNT (x⁺ ⊕ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

  forgetAlg : ∀{Γ Δ c #c}{D : DatDesc I Γ #c} (o : Orn J u Δ c D) →
              ∀{δ} → Alg (ornToDesc o) δ (μ D (c δ) ∘ u)
  forgetAlg o = ⟨_⟩ ∘ forgetNT o

  forget : ∀{Γ Δ c #c}{D : DatDesc I Γ #c} (o : Orn J u Δ c D) →
           ∀{δ j} → μ (ornToDesc o) δ j → μ D (c δ) (u j)
  forget o = fold (forgetAlg o)
\end{code}\end{codelst}


\begin{example}
\todo{example bla bla}
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

\section{Algebraic ornaments}\label{sec:ext-algorn}

Now that indices are supported, \emph{algebraic ornaments} can be
defined. When an algebra is given for a description |D|, it induces an
algebraic ornament on |D| which adds the results of the algebra as an
index. The type of |algOrn| below shows how an algebra which results
in a value of type |R| gives an ornament which goes from a |Desc I Γ
dt| to a |Desc (I ▷ R) Γ dt|.

\begin{code}
  algOrn : ∀{I R Γ dt}{D : Desc I Γ dt} →
           ({γ : ⟦ Γ ⟧} → Alg D γ R) → DefOrn (I ▷ R) pop Γ id D
\end{code}

Interestingly, algebraic ornaments only work when the Algebra is
polymorphic in the datatype parameters. During the definition of an
ornament we do not know which environment will be used, so it should
work for any environment. To produce an index of type |R| for any
environment, the algebra must work for any environment. One quickly
gets stuck when trying to define |algOrn| for a fixed environment.

What exactly should an algebraic ornament do? Consider the |Vec|
datatype. We would like to get a descriptions of |Vec| by using the
algebraic ornament of the length algebra for lists. We reiterate the
definitions of |Vec| and |lengthAlg| below. By comparing them, one may
note that the result indices |0| and |suc n| of the |[]| and |_∷_|
constructors match with the right sides of the first and second clause
of |lengthAlg|. In an algebra, every recursive argument is matched
with the result of the algebra on that argument; this can be used to
write the right hand side. In the resulting datatype (|Vec|) the
result for the recursive argument |xs| is kept in a new argument
|n|.

\begin{code}
data Vec (A : Set) : Nat → Set where
  [] : Vec A 0
  _∷_ : ∀{n} → (x : A) → (xs : Vec A n) → Vec A (suc n)

lengthAlg : {A : Set} → Alg listDesc (tt , A) (const Nat)
lengthAlg (zero , refl) = 0
lengthAlg (suc zero , x , n , refl) = suc n
lengthAlg (suc (suc ()) , _)
\end{code}

The way to build an algebraic ornament is by inserting a new argument
for every recursive argument, which can contain the result of the
algebra for that argument. The new arguments are used in the
computation of the result indices in the way the algebra tells us to.

Algebraic ornaments are implemented in \fref{lst:ext-algorn}. The
implementation itself is in |algOrn′|, which has a slightly different
type than |algOrn|. Because new arguments are being inserted, the
recursive calls may have a changed context. The |algOrn′| function
supports context changes by having two additional arguments |Δ| and
|c|. The type of |algOrn| is a bit more convenient to use in
practice---It helps with some type inference.

The algebra is used up piece by piece while recursing over the
description. Though the algebra |α| only requires one argument, this
argument is a product type in most cases (for all descriptions but
|ι|), so |curry| can be used to instantiate part of the product. The
case for |S ⊗ xs| shows it clearly: An |α| of type |Alg (S ⊗ xs) _ _|,
which normalises to |Σ (S _) _ → R _|, is curried to get a function |S
_ → Alg xs _ _|. The |top γ| is of the correct type |S _|, so with
|curry α (top γ)| we get an algebra which works for the tail of the
description |xs|.

The case for |rec i ⊗ xs| shows how a new argument |R ∘ i ∘ c| is
inserted. Here |c| transforms the ornamented environment of type |⟦ Δ
⟧| into an environment of type |⟦ Γ ⟧|, |i| tells us the index which
was used for the recursive argument under that environment, and |R|
gives the type of the result under that index. The recursive argument
is copied, but with a new index consisting of two parts: |i (c (pop
δ))| and |top δ|. The first part is effectively the old index, but
calculated by using the |pop δ| environment (the ornamented
environment excluding the newly inserted argument). The second
part |top δ| is the value of the newly inserted argument.

\begin{codelst}{Algebraic ornaments}{ext-algorn}\begin{code}
module _ {I R} where
  algOrn′ : ∀{Γ Δ dt}{c : Cxf Δ Γ}(D : Desc I Γ dt) →
           (∀{δ : ⟦ Δ ⟧} → Alg D (c δ) R) → Orn (I ▷ R) pop Δ c D
  algOrn′ {dt = isCon} {c = c} (ι o) α = ι (λ δ → inv (o (c δ) , α refl))
  algOrn′ {dt = isCon} (S ⊗ xs) α = -⊗ (algOrn′ xs (λ {γ} → curry α (top γ)))
  algOrn′ {dt = isCon} {c = c} (rec i ⊗ xs) α = R ∘ i ∘ c +⊗
    rec (λ δ → inv (i (c (pop δ)) , top δ)) ⊗
    algOrn′ xs (λ {δ} → curry α (top δ))
  algOrn′ {dt = isDat _} `0 α = `0
  algOrn′ {dt = isDat _} (x ⊕ xs) α = algOrn′ x (curry α 0)
    ⊕ algOrn′ xs (α ∘ (suc *** id))

  algOrn : ∀{Γ dt}{D : Desc I Γ dt} →
           ({γ : ⟦ Γ ⟧} → Alg D γ R) → Orn (I ▷ R) pop Γ id D
  algOrn {D = D} = algOrn′ D
\end{code}\end{codelst}

\begin{example}
The |Vec| type can be described with |algOrn|. The length algebra can
be used to do this. The signature of |list→vec′| is the same as that
for the previously defined |list→vec|. A new index of type |const Nat|
is introduced, because that is the result type of |lengthAlg|.

\begin{code}
list→vec₁ : Orn (ε ▷ const Nat) pop (ε ▷₁′ Set) id listDesc
list→vec₁ = algOrn lengthAlg
\end{code}

The ornament results in a description of |Vec|. Do note that the order
of the arguments of the |_∷_| constructor is slightly different,
because the new argument |n| is being inserted right before the
recursive argument.

\begin{code}
vecDesc₁ : DatDesc (ε ▷′ Nat) (ε ▷₁′ Set) 2
vecDesc₁ = ι (const (tt , 0))
  ⊕ top
  ⊗ const Nat
  ⊗ rec (λ γ → tt , top γ)
  ⊗ ι (λ γ → tt , suc (top γ))
  ⊕ `0

test-list→vec₁ : ornToDesc list→vec₁ ≡ vecDesc₁
test-list→vec₁ = refl
\end{code}
\end{example}

\section{Reornaments}\label{sec:ext-reornaments}

\emph{Reornaments} are another interesting class of ornaments which
can be defined now that indices are supported. These are the result of
building an algebraic ornament using the ornamental algebra of an
ornament \cite{mcbride11}. A typical example is the reornament of the
|nat→list| ornament. The ornamental algebra of that ornament is
effectively the length algebra, so the reornament of |nat→list| gives
an ornament from |Nat| to |Vec|.

A reornament is an ornament |o| followed by the algebraic ornament of
the ornamental algebra of |o|. \emph{Ornament composition} is defined
as |_>>⁺_| to help with the definition of reornaments. The function
|_>>⁺_| takes two ornaments and results in a new ornament which
combines the two:

\begin{code}
module _ {I J J′}{u : Cxf J I}{v : Cxf J′ J} where
  _>>⁺_ : ∀{Γ Δ Δ′ c d dt} {D : Desc I Γ dt} →
    (o : Orn J u Δ c D) → Orn J′ v Δ′ d (ornToDesc o) →
    Orn J′ (u ∘ v) Δ′ (c ∘ d) D
\end{code}

The full definition of composition is very straightforward, so it is
not listed here. To prove that composition of ornaments is correctly
defined, |>>⁺-coherence| says that |ornToDesc| of the composed
ornament is the same as |ornToDesc| of the second ornament, which in
turn is an ornament on |ornToDesc| of the first ornament. The
descriptions contain higher order terms (terms depending on
environments) which are not intensionally equal. We can however prove
that they are pointwise equal, for each environment they give the same
result. A small module is used wherein the extensionality lemma (|(∀ x
→ f x ≡ g x) → f ≡ g|) is available, effectively making the normal
equality |_≡_| extensional (within the module).

\begin{code}
  module _ (ext : ∀{a b} → Extensionality a b) where
    >>⁺-coherence : ∀{Γ Δ Δ′ c d dt} {D : Desc I Γ dt} →
      (o : Orn J u Δ c D) → (p : Orn J′ v Δ′ d (ornToDesc o)) →
      (ornToDesc (o >>⁺ p)) ≡ ornToDesc p
\end{code}

The |reornament| function implements reornamentation using composition
and the algebraic ornament of the ornamental algebra. An index is
added which can contain elements of the original description (|μ D tt
(u j)|). No parameters are allowed for the original description, so
the environment can be instantiated with |tt|.

\begin{code}
reornament : ∀{I J u Δ}{c : Cxf Δ ε}{#c}{D : DatDesc I ε #c} →
  (o : Orn J u Δ c D) → Orn (J ▷ μ D tt ∘ u) (u ∘ pop) Δ c D
reornament o = o >>⁺ (algOrn (λ {δ} → forgetAlg o {δ}))
\end{code}

With the current descriptions, reornaments on descriptions with
parameters can not be supported in general. While writing a type for a
|reornament'| operation which does support it, we get stuck when
trying to give the environment for the index. The hole |?0| is of type
|⟦ Γ ⟧|, an environment for the original description. Such an
environment could be built using the ornamented environment of type |⟦
Δ ⟧| and the environment transformer |c|, but there is no |⟦ Δ ⟧|
available in the place of the hole. The problem lies in the fact that
descriptions do not allow indices to be dependent on parameters, as is
discussed in the next section. This is a fundamental problem of our
descriptions, so |reornament| can not work around it.

\begin{code}
  reornament′ : ∀{I J u Δ Γ}{c : Cxf Δ Γ}{#c}{D : DatDesc I Γ #c} →
    (o : Orn J u Δ c D) → Orn (J ▷ μ D ?0 ∘ u) (u ∘ pop) Δ c D
\end{code}

\begin{example}
The reornament of |nat→list| was already mentioned. Let us assume that
we have the following definitions for the description of natural
numbers, the constructors for that description, and the ornament from
natural numbers to lists:

\begin{code}
natDesc : DatDesc ε ε 2

natDesc-zero : μ natDesc tt tt
natDesc-suc : μ natDesc tt tt → μ natDesc tt tt

nat→list : Orn ε id (ε ▷₁′ Set) (λ δ → tt) natDesc
\end{code}

By applying |reornament| to |nat→list|, one obtains a ornament from
natural numbers to |Vec|. Contrary to |list→vec₁| from
\fref{sec:ext-algorn}, which added a |Nat| as an index, this one uses
a |μ natDesc tt tt|. These are isomorphic, so it should not be a
problem.

\begin{code}
nat→vec₂ : Orn (ε ▷′ μ natDesc tt tt) (λ j → tt) (ε ▷₁′ Set) (λ δ → tt) natDesc
nat→vec₂ = reornament nat→list
\end{code}

The resulting description is very similar to the one created by
|algOrn lengthAlg|. The only differences are that |Nat| has been
replaced with |μ natDesc tt tt|, |0| with |natDesc-zero| and |suc|
with |natDesc-suc|.

\begin{code}
vecDesc₂ : DatDesc (ε ▷′ μ natDesc tt tt) (ε ▷₁′ Set) 2
vecDesc₂ = ι (const (tt , natDesc-zero))
  ⊕ top
  ⊗ const (μ natDesc tt tt)
  ⊗ rec (λ γ → tt , top γ)
  ⊗ ι (λ γ → tt , natDesc-suc (top γ))
  ⊕ `0

test-nat→vec : ornToDesc nat→vec₂ ≡ vecDesc₂
test-nat→vec = refl
\end{code}
\end{example}

\section{Discussion}

One of the limitations of the current implementation of indices and
parameters is that indices can not use the parameters. For instance in
the description of the following datatype |Silly|, one gets stuck
when trying to give the type of the index. The hole |?0| must be of
type |Nat|, while only |γ| of type |⊤′| is available.

\begin{code}
data Silly (n : Nat) : Fin n → Set where
  silly : (k : Fin n) → (b : Bool) → Foo n k

sillyDesc : DatDesc (ε ▷ (λ γ → Fin ?0)) (ε ▷′ Nat) 1
sillyDesc = ...
\end{code}

It is not easy to make the indices depend on the parameters within the
current implementation, because parameters are not a separate thing
within the descriptions. The datatype parameters are merely the
initial context, which is being expanded in the constructors.

Consider the type for the argument of the current |ι| constructor: |(γ
: ⟦ Γ ⟧) → ⟦ I ⟧|. A value of this type gives an index of type |⟦ I ⟧|
under a given environment. The environment |γ| contains both the
values for the datatype parameters and for other variables in the
constructor. If indices could depend on the parameters, the result
type (currently |⟦ I ⟧|) should depend on the parameter part of
|γ|. Other local variables must not be used to determine the index
type, because the types of the indices in datatype are declared in the
signature (before the |where|) where only the parameters can be
used. Right now, there is no way to just take the parameter part of an
environment.

The fundamental problem here is that parameter types are in the same
|Cx| as the internal contexts, while internal contexts can not be used
everywhere where the parameter types can be used. The author did not
succeed in obtaining subsets of environments, so this is not a trivial
problem. The choice to have internal contexts build upon the |Cx| from
the parameters seemed reasonable at the time because it allows the
local parts of the contexts (i.e. arguments) to use the
parameters. For many purposes it works well, but this approach is not
suited when indices must depend on parameters.

There is a promising solution to this problem. Descriptions can have a
separate |Cx| just for the parameters, let us call it |(P : Cx)|, and
the indices and internal contexts take the form of functions form |⟦ P
⟧| to |Cx|. One might say: indices and internal contexts are both
\emph{contexts under the parameter environment}, meaning that the
parameters can be used to determine these contexts.

Descriptions using such a separate parameter context are defined in
\fref{lst:ext-sep-descriptions}. The |P| and |I| are module parameters
because they stay constant within the whole description just like
parameters and indices of real datatypes---For all practical purposes
they work as if they were datatype parameters for both |ConDesc| and
|DatDesc|. Places where an internal environment could be used (the
functions which had |(γ : ⟦ Γ ⟧)| as input) can now use both the
parameter values |(p : ⟦ P ⟧)| and the environment |(γ : ⟦ Γ p
⟧)|. When an index has to be specified, the type to be given is |⟦ I p
⟧|, so the type of the indices can depend on the parameter values.

\begin{codelst}{Descriptions with separate parameters}{ext-sep-descriptions}\begin{code}
module _ (P : Cx) (I : (p : ⟦ P ⟧) → Cx) where
  data ConDesc (Γ : (p : ⟦ P ⟧) → Cx) : Set where
    ι : (o : (p : ⟦ P ⟧)(γ : ⟦ Γ p ⟧) → ⟦ I p ⟧) → ConDesc Γ
    _⊗_ : (S : (p : ⟦ P ⟧)(γ : ⟦ Γ p ⟧) → Set) →
      (xs : ConDesc (λ p → Γ p ▷ S p)) → ConDesc Γ
    rec_⊗_ : (i : (p : ⟦ P ⟧)(γ : ⟦ Γ p ⟧) → ⟦ I p ⟧) →
      (xs : ConDesc Γ) → ConDesc Γ
  data DatDesc : (#c : Nat) → Set where
    `0 : DatDesc 0
    _⊕_ : ∀{#c} (x : ConDesc (const ε)) →
      (xs : DatDesc #c) → DatDesc (suc #c)
\end{code}\end{codelst}

The |DatDesc| type does not pass a context around, but it starts every
|ConDesc| off with an empty context (|const ε|). Note how similar this
is to the descriptions of \fref{chap:simple}
(\Fref{lst:simple-desc}). Once again, constructor descriptions have
their own environments which datatype descriptions do not
need and a full constructor is always closed, in the sense that |Γ| is
|const ε|.


The semantics in \fref{lst:ext-sep-semantics} show how descriptions
with separate parameters are interpreted. It is a straightforward
derivation from the semantics in \fref{lst:ext-semantics} and
\fref{lst:simple-semantics}. While the interpretation of |ConDesc|
requires parameter values |(p : ⟦ P ⟧)| and a local environment |(γ :
⟦ Γ p ⟧)|, the interpretation of |DatDesc| does not need a local
environment. Notice how both result in an endofunctor on |⟦ I p ⟧ →
Set|, of which |μ| is the fixpoint.

\begin{codelst}{Semantics of descriptions with separate parameters}{ext-sep-semantics}\begin{code}
⟦_⟧conDesc : ∀{P I Γ} → ConDesc P I Γ →
  (p : ⟦ P ⟧) → (γ : ⟦ Γ p ⟧) → (X : ⟦ I p ⟧ → Set) → ((o : ⟦ I p ⟧) → Set)
⟦ ι o ⟧conDesc p γ X o′ = o p γ ≡ o′
⟦ S ⊗ xs ⟧conDesc p γ X o = Σ (S p γ) λ s → ⟦ xs ⟧conDesc p (γ , s) X o
⟦ rec i ⊗ xs ⟧conDesc p γ X o = X (i p γ) × ⟦ xs ⟧conDesc p γ X o
⟦_⟧datDesc : ∀{P I #c} → DatDesc P I #c →
  (p : ⟦ P ⟧) → (X : ⟦ I p ⟧ → Set) → ((o : ⟦ I p ⟧) → Set)
⟦_⟧datDesc D p X o = Σ (Fin _) λ k → ⟦ lookupCtor D k ⟧conDesc p tt X o

data μ {P I #c} (D : DatDesc P I #c) (p : ⟦ P ⟧) (o : ⟦ I p ⟧) : Set where
  ⟨_⟩ : ⟦ D ⟧ p (μ D p) o → μ D p o
\end{code}\end{codelst}

The |Silly| datatype of the beginning of this section can now be
described. The index type uses |top p| to refer to the parameter of
type |Nat|. Argument types and indices can be specified using both the
parameter values |p| and the local environment |γ|.

\begin{code}
SillyDesc : DatDesc (ε ▷′ Nat) (λ p → ε ▷′ Fin (top p)) 1
SillyDesc = (λ p γ → Fin (top p)) ⊗ (λ p γ → Bool)
  ⊗ ι (λ p γ → tt , top (pop γ)) ⊕ `0

silly-test : μ SillyDesc (tt , 10) (tt , 3)
silly-test = ⟨ 0 , 3 , true , refl ⟩
\end{code}

Another interesting, less silly, datatype which can be described is
the equality type. The index of our equality datatype |MyEq| uses the
value |A| from the parameters to determine its type. The description
|EqDesc| is quite simple, and the embedding-projection pair is given
to show that it is correct.

\begin{code}
data MyEq {A : Set} (x : A) : A → Set where
  refl : MyEq x x

EqDesc : DatDesc (ε ▷′ Set ▷ top) (λ p → ε ▷′ top (pop p)) 1
EqDesc = ι (λ p γ → tt , top p) ⊕ `0

to-eq : ∀{A x y} → MyEq x y → μ EqDesc ((tt , A) , x) (tt , y)
to-eq refl = ⟨ 0 , refl ⟩
from-eq : ∀{A x y} → μ EqDesc ((tt , A) , x) (tt , y) → MyEq x y
from-eq ⟨ zero , refl ⟩ = refl
from-eq ⟨ suc () , _ ⟩
\end{code}

This way of encoding parameters separately from contexts seems to be a
better approximation of Agda datatypes than the descriptions of
\fref{lst:ext-desc}. This particular encoding was found in the late stages of
writing this thesis, so no further efforts have been made regarding
the implementation of ornaments and related functionality. For future
research, this encoding might be promising. It would be interesting to
see if everything works out, and if |reornament| might then be
implemented in a way which allows parameters in the original
description (see \fref{sec:ext-reornaments}).
