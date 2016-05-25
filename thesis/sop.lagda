%include thesis.fmt

\chapter{Generics and ornaments}\label{chap:sop}

Datatype-generic programming in functional languages is all about
figuring out how to build complicated types from a small set of
components. For finite types - those types which have a finite number
of inhabitants, i.e. they do not allow recursion - this is quite
easy. By using just the basic components |⊤|, |_×_| and |Either| for
unit, products and coproducts, we can already build some simple types
like those for booleans and maybe. The type for maybe contains a
parameter which has to be instantiated to get the actual |Set|.

\begin{code}
  boolLike : Set
  boolLike = Either ⊤ ⊤

  maybeLike : (A : Set) → Set
  maybeLike A = Either A ⊤
\end{code}

Of course, finite types are very limited. Not just in the number of
elements contained in these types, but in their usefulness too. To
implement a wider range of types we need recursion. We could say that,
for instance, |listLike A = Either ⊤ (listLike A)| but the evaluation
of a term like that does not terminate. The common approach to work
around this problem is by associating each datatype with a
\emph{pattern functor} \cite{jansson97, norell03}. Instead of building
a |Set|, we build a |Set → Set|. For example these types for naturals
and lists:

\begin{code}
  natPF : Set → Set
  natPF X = Either ⊤ X

  listPF : (A : Set) → Set → Set
  listPF A X = Either ⊤ (A × X)
\end{code}

The meaning of the content of the argument |X| varies depending on the
circumstances, but at least we can say that each occurence of |X|
signifies that it is a recursive position. The definitions |natPF| and
|listPF| provide the structure - or \emph{pattern} - for the types we
want without talking about the recursive spots. By taking the fixpoint
of the pattern functor we let the argument |X| refer to the type
itself, effectively representing recursion. The fixpoint is
represented as a datatype to allow us to manually unroll the type
\footnote{The observant reader may notice that the |μ| datatype does
  not pass the strict-positivity check. This problem is solved with a
  new definition of |μ| in the next section.}.

\begin{code}
  data μ′ (F : Set → Set) : Set where
    ⟨_⟩ : F (μ′ F) → μ′ F
\end{code}

Now whenever a |μ′ somePF| is expected, we can provide a |somePF (μ′
somePF)| wrapped in |⟨_⟩|. The recursive positions within that |somePF
(μ′ somePF)| are expected to contain a |μ′ somePF| again, closing the
loop neatly.

\begin{code}
  listPF-example : μ′ (listPF String)
  listPF-example = ⟨ right ("one" , ⟨ right ("two" , ⟨ left tt ⟩) ⟩) ⟩
\end{code}

We have seen how recursive types can be built using a few basic
components, namely the unit type, products, coproducts and
fixpoints. To be able to reason about these types we have to formalise
the fact that only these components, and no others, can be used to
form our types. In \fref{sec:sop-descriptions} we reify these
components to build a \emph{universe of descriptions}.  In general,
the concept of a universe in Martin Löf's type theory
\cite{martinloef84} involves two things: firstly there are codes which
describe types; secondly there is a decoding function to translate
codes into whatever they are meant to encode. In this work, the
descriptions are the codes of the universe. The decoding function
gives us the pattern functor for a description, one might also say
that the decoding function provides a \emph{semantics} for
descriptions. By taking the fixpoint of the resulting pattern functor
we obtain a |Set| which is a usable type.

With descriptions and their interpretations in place, ornaments for
these descriptions are defined in \fref{sec:sop-ornaments}. Every
ornament is built for a specific description, and can represent the
copying, insertion and removal of parts of the description. If something
is to be called an ornament, it must be possible to produce a |forget|
function for every ornament. The |forget| function goes from elements
of the ornamented type to elements of the original type. In
\fref{sec:sop-ornalgs} an \emph{ornamental algebra} is defined which
gives rise to the |forget| function.


\section{Descriptions}\label{sec:sop-descriptions}

As promised, we will build a universe of descriptions. In this
universe, every allowed component is represented by a code. For the
descriptions in this chapter, we will be using the following
codes:

\begin{itemize}
\item The empty type is described with |`0|
\item The unit type is described with |ι|
\item The |_⊕_| operator represents a choice. For our purposes this
  always means a choice between different constructors.
\item The |_⊗_| operator is used for products. To the right of the
  operator goes another description, so chains of |_⊗_|'s can be
  formed to represent a single constructor. The left side is of type
  |Set|, so a type can be given to represent a constructor argument of
  the given type.
\item For recursive arguments we use a special operator |rec-⊗_|.
\end{itemize}

These codes are formalised using the |ConDesc| and |DatDesc|
datatypes, defined in \fref{lst:sop-descriptions}. |ConDesc| contains
the constructors |ι|, |_⊗_| and |rec-⊗_|; these are sufficient to
describe constructors of the supported types. |DatDesc| is basically a
|Vec| of |ConDesc|s; it is indexed by the number of constructors and
uses |`0| and |_⊕_| to chain the |ConDesc|s together. The reasons for
this split between |ConDesc|s and |DatDesc|s are discussed at the end
of this chapter.

\begin{codelst}{Sum-of-products descriptions}{sop-descriptions}\begin{code}
data ConDesc : Set₁ where
  ι : ConDesc
  _⊗_ : (S : Set) → (xs : ConDesc) → ConDesc
  rec-⊗_ : (xs : ConDesc) → ConDesc

data DatDesc : Nat → Set₁ where
  `0 : DatDesc 0
  _⊕_ : ∀{#c} (x : ConDesc) (xs : DatDesc #c) → DatDesc (suc #c)
\end{code}\end{codelst}

With this set of components we can build some simple datatypes. To
get some feeling for this, we look at the descriptions for unit,
naturals, non-dependent pairs and lists. Note that |_⊗_| and |rec-⊗_|
take precedence over |_⊕_|, so products are applied before sums.

\begin{code}
unitDesc : DatDesc 1
unitDesc = ι ⊕ `0

natDesc : DatDesc 2
natDesc = ι ⊕ rec-⊗ ι ⊕ `0

pairDesc : (A B : Set) → DatDesc 1
pairDesc A B = A ⊗ B ⊗ ι ⊕ `0

listDesc : (A : Set) → DatDesc 2
listDesc A = ι ⊕ A ⊗ rec-⊗ ι ⊕ `0
\end{code}

It's noteworthy that even though we can parameterise these
descriptions, the descriptions themselves are not really aware of
it. The parameterisation takes place outside of the descriptions. The
extended descriptions in \fref{chap:extended} internalise the
parameterisation, so the parameters are included within the
descriptions.

\Fref{lst:sop-semantics} shows how descriptions are decoded to pattern
functors. The decoding of |ConDesc| is fairly straightforward,
producing |λ X → S × X × ⊤| for |S ⊗ rec-⊗ ι|. The decoding of
|DatDesc| is somewhat more involved. While the conventional approach
would be to convert all |_⊕_| constructors to |Either| and the |`0|
constructor to |⊥|, we instead choose to produce a Σ-type: |Σ (Fin #c)
λ k → ⟦ lookupCtor D k ⟧conDesc X|. This type means that the first
argument is used to indicate the choice of constructor and the second
argument must then be an element of that particular constructor. This
prevents long chains of |left|s and |right|s due to nested
|Either|s. We will write |⟦_⟧| to mean |⟦_⟧conDesc| or |⟦_⟧datDesc|
when that is not ambiguous in the context..

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

-- The notation |⟦_⟧| is overloaded to mean either |⟦_⟧conDesc| or |⟦_⟧datDesc|
data μ {#c : Nat}(F : DatDesc #c) : Set where
  ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F
\end{code}\end{codelst}

The fixpoint |μ| is similar to the fixpoint in the introduction of this chapter,
but specialised to the decoding of |DatDesc|. This specialisation is
necessary to convince Agda that the datatype |μ| is strictly
positive. This works as long as there are no non-strictly-positive
occurences of |X| in |⟦_⟧datDesc| and |⟦_⟧conDesc|. Since |μ| already
includes the call to |⟦_⟧datDesc|, we can get the |Set| corresponding
to a description by simply prepending the description with |μ|. For
instance, |μ natDesc| is a |Set| which corresponds to the natural
numbers.

\Fref{lst:sop-nat-example} gives an example of how a |μ natDesc| can
be constructed. In |nat-example₁|, the hole has to be of type |⟦
natDesc ⟧ (μ natDesc)|. When we expand that type we get a Σ-type where
the first argument must be a |Fin 2|, allowing us to pick one of the
two constructors. In |nat-example₂| we pick the second constructor
(they start at number 0), the description of this constructor is
|rec-⊗ ι|, so we are left to fill in a |⟦ rec-⊗ ι ⟧ (μ natDesc)| which
is equivalent to |μ natDesc × ⊤|. The definition |nat-example₃| shows
how this process could be completed by filling in |⟨ 0 , tt ⟩| in the
recursive spot, resulting in an expression which should be read as
|suc zero|, i.e. the number 1.

\begin{codelst}{Constructing naturals}{sop-nat-example}\begin{code}
nat-example₁ : μ natDesc
nat-example₁ = ⟨ ? ⟩
-- Goal: |⟦ natDesc ⟧ (μ natDesc)|
-- Expands to: |Σ (Fin 2) (λ k → ⟦ lookupCtor natDesc k ⟧ (μ natDesc))|

nat-example₂ : μ natDesc
nat-example₂ = ⟨ 1 , ? ⟩
-- Goal: |⟦ lookupCtor natDesc 1 ⟧ (μ natDesc)|
-- Expands to: |⟦ rec-⊗ ι ⟧ (μ natDesc)|
-- Expands to: |μ natDesc × ⊤|

nat-example₃ : μ natDesc
nat-example₃ = ⟨ 1 , ⟨ 0 , tt ⟩ , tt ⟩
\end{code}\end{codelst}

Whenever we want to give a value belonging to |μ someDescription|, we
start by writing |⟨_⟩| and picking the number of the constructor we want to
use. This corresponds with the fact that for some datatype |DT|, a
value of type |DT| can be created by using one of the constructors of
that datatype. The following functions for naturals and lists show how every
constructor-call is represented by a particular term |⟨ i , ? ⟩|:

\begin{code}
`zero : μ natDesc
`zero = ⟨ 0 , tt ⟩
`suc : μ natDesc → μ natDesc
`suc n = ⟨ 1 , n , tt ⟩

`[] : ∀{A} → μ (listDesc A)
`[] = ⟨ 0 , tt ⟩
_`∷_ : ∀{A} → A → μ (listDesc A) → μ (listDesc A)
_`∷_ x xs = ⟨ 1 , x , xs , tt ⟩
\end{code}

With these functions, we can write values almost like we would with
normal datatypes. It illustrates the similarity between the
descriptions and real datatypes:

\begin{code}
nat-example : `suc `zero ≡ ⟨ 1 , ⟨ 0 , tt ⟩ , tt ⟩
nat-example = refl

list-example : 7 `∷ 8 `∷ `[] ≡ ⟨ 1 , 7 , ⟨ 1 , 8 , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩
list-example = refl
\end{code}

If we want to be absolutely certain that our descriptions match up to
the types we want to represent, we could provide an isomorphism
between them. In the case of lists for some given type |A|, an
isomorphism between |List A| and |μ (listDesc A)| would entail four
functions. The functions |to| and |from| convert between the
representation using generics and the Agda datatype. Within the
context of generic programming the |from| and |to| functions are
commonly referred to as the \emph{embedding-projection pair}. The
functions |to-from| and |from-to| provide proofs that |to| and |from|
are inverses of each other.

\begin{code}
    to : List A → μ (listDesc A)
    from : μ (listDesc A) → List A
    to-from : ∀ x → from (to x) ≡ x
    from-to : ∀ x → to (from x) ≡ x
\end{code}


\section{Maps and folds}\label{sec:sop-map}

In the previous section, we claimed that the decoding of a description
results in a so-called pattern functor. Clearly, |⟦_⟧datDesc| returns
something of type |Set → Set|, but we have not yet shown that it is
really a functor. To prove this, we define the functorial map for the
decoding of any description in \fref{lst:sop-map}. For a function |f :
X → Y| and a description |D|, we can always return a function |⟦ D ⟧ X
→ ⟦ D ⟧ Y|.

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

A typical operation which can be performed generically is
\emph{folding}. Given a description |D| and an algebra of type |DatAlg
D X|, the |fold| function can calculate a result of type |X| for any
value of type |μ D|. We define |DatAlg D X| to be |⟦ D ⟧ X → X|. The
intuition here is that the user has to provide the fold function with
a method to calculate a result for every possible value, given that a
result has already been calculated for the recursive positions. The
|fold| function first maps the fold over the recursive positions and
then the algebra can be applied.

\begin{code}
DatAlg : ∀{#c} → DatDesc #c → Set → Set
DatAlg D X = ⟦ D ⟧ X → X

fold : ∀{#c}{D : DatDesc #c}{X} (α : DatAlg D X) → μ D → X
fold {D = D} α ⟨ xs ⟩ = α (datDescmap (fold α) D xs)
\end{code}

\begin{example}
An example of a simple algebra is one which counts the |true| values
in a list of booleans. To define the algebra we can pattern match on
the argument of type |⟦ listDesc| |Nat ⟧ Nat|. Each case corresponds to
a constructor of the list datatype. In the second case |(suc zero , x
, xs , tt)|, the variable |x| is of type |Bool| because it is an
element in the list. The variable |xs| is of type |Nat| because that
is the result of the algebra. By applying |fold| to the algebra we
obtain a function which counts the number of |true|s in a list of
booleans.

\begin{code}
countTruesAlg : DatAlg (listDesc Bool) Nat
countTruesAlg (zero , tt) = 0
countTruesAlg (suc zero , x , xs , tt) = if x then suc xs else xs
countTruesAlg (suc (suc ()) , _)

countTrues : μ (listDesc Bool) → Nat
countTrues = fold countTruesAlg
\end{code}
\end{example}

\todo{Provide a more interesting example, perfect binary trees maybe?}

\section{Ornaments}\label{sec:sop-ornaments}

Now that we have a good way to describe some basic datatypes within
Agda, we can implement ornaments for those descriptions. Ornaments for
such simple datatypes without indices are of limited use, but getting
some practice with this basic form now should make things easier when
we extend the descriptions with more features. Our ornaments are
mostly based on those presented by McBride \cite{mcbride11} and later
by Dagand and McBride \cite{dagand14-transporting}. Our choice of
descriptions does require some unique adaptations to the ornaments.

The ornaments and the interpretation of them are defined in
\fref{lst:sop-ornaments}. Ornaments for constructors and datatypes are
defined separately; |ConOrn| works on |ConDesc|s and |DatOrn| works on
|DatDesc|s. Both are indexed by their respective descriptions, such
that an ornament for a datatype description |D| has type |DatOrn
D|. The ornaments contain several groups of operations:

\begin{itemize}
\item The unit copy operation |ι| just keeps the |ι| constructor.
\item Argument copy operations: |-⊗_| and |rec-⊗_| keep the argument,
  but an ornament has to be given for the tail. The |Set| for |_⊗_|
  does not have to be given; it is simply copied.
\item Argument insertion operations: |_+⊗_| and |rec-+⊗_| insert a new
  argument in a constructor.
\item The argument deletion operation |give-K| removes a non-recursive
  argument from a constructor.
\item Datatype copy operations |`0| and |_⊕_|. Constructors can not be
  inserted or removed with the chosen ornaments, so the |`0| and |_⊕_|
  have to be copied. An ornament has to be given for every constructor
  in the datatype. The choice to disallow insertion and removal of
  constructors is discussed in \fref{sec:sop-discussion}.
\end{itemize}

\begin{codelst}[t]{Definition of ornaments}{sop-ornaments}\begin{code}
data ConOrn : (D : ConDesc) → Set₁ where
  ι : ConOrn ι
  -⊗_ : ∀{S xs} → (xs⁺ : ConOrn xs) → ConOrn (S ⊗ xs)
  rec-⊗_ : ∀{xs} → (xs⁺ : ConOrn xs) → ConOrn (rec-⊗ xs)

  _+⊗_ : ∀{xs}(S : Set) → (xs⁺ : ConOrn xs) → ConOrn xs
  rec-+⊗_ : ∀{xs} → (xs⁺ : ConOrn xs) → ConOrn xs

  give-K : ∀{S xs} (s : S) → (xs⁺ : ConOrn xs) → ConOrn (S ⊗ xs)

data DatOrn : ∀{#c}(D : DatDesc #c) → Set₁ where
  `0 : DatOrn `0
  _⊕_ : ∀{#c x xs} →
        (x⁺ : ConOrn x) (xs⁺ : DatOrn xs) → DatOrn {suc #c} (x ⊕ xs)

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
\end{code}\end{codelst}

We can now build some simple ornaments. We have previously defined
|natDesc| as |ι ⊕ rec-⊗ ι ⊕ `0| and |listDesc A| as |ι ⊕ A ⊗ rec-⊗ ι ⊕
`0|. These are clearly quite similar. We can build an ornament on
|natDesc| which extends the second constructor with an argument of
type |A|, using the copy operations and |_+⊗_|. Interpreting this
ornament with |ornToDesc| gives us exactly the description of lists of
A:

\begin{code}
nat→list : ∀{A} → DatOrn natDesc
nat→list {A} = ι ⊕ A +⊗ rec-⊗ ι ⊕ `0

test-nat→list : ∀{A} → ornToDesc nat→list ≡ listDesc A
test-nat→list = refl
\end{code}

\section{Ornamental algebras}\label{sec:sop-ornalgs}

Each ornament induces an \emph{ornamental algebra}
\cite{mcbride11}. The ornamental algebra turns elements of the
ornamented type back into elements of the original type. Such that
folding the ornamental algebra for an ornament |o : DatOrn D| results
in a function from |μ (ornToDesc o)| to |μ D|. The ornamental algebra
is built using a natural transformation from |⟦ o ⟧| to |⟦ D ⟧|, that
is a function which goes from |⟦ o ⟧ X| to |⟦ D ⟧ X| for all values of
|X|.

\begin{code}
forgetNT : ∀{#c}{D : DatDesc #c} (o : DatOrn D) →
           ∀{X} → ⟦ o ⟧ X → ⟦ D ⟧ X
forget : ∀{#c}{D : DatDesc #c} (o : DatOrn D) →
         μ (ornToDesc o) → μ D
\end{code}

So the |forget| function can be implemented using |forgetNT|. In other
words; when we can transform one pattern functor into another pattern
functor, we can make that same transformation between the fixed points
of those pattern functors. The full definition is given in
\fref{lst:sop-forget}. Note that we use the function |_***_|, which is
defined as the bimap on pairs such that |(f *** g) (x , y)| is |(f x ,
g y)|. The actual ornamental \emph{algebra} |forgetAlg| arises as an
intermediary step between |forgetNT| and |forget|.

\begin{codelst}[t]{Ornamental algebras}{sop-forget}\begin{code}
conForgetNT : ∀{D} (o : ConOrn D) →
              ∀{X} → ⟦ conOrnToDesc o ⟧ X → ⟦ D ⟧ X
conForgetNT ι tt = tt
conForgetNT (-⊗ xs⁺) (s , v) = s , conForgetNT xs⁺ v
conForgetNT (rec-⊗ xs⁺) (s , v) = s , conForgetNT xs⁺ v
conForgetNT (_+⊗_ S xs⁺) (s , v) = conForgetNT xs⁺ v
conForgetNT (rec-+⊗_ xs⁺) (s , v) = conForgetNT xs⁺ v
conForgetNT (give-K s xs⁺) v = s , conForgetNT xs⁺ v

forgetNT : ∀{#c}{D : DatDesc #c} (o : DatOrn D) →
           ∀{X} → ⟦ ornToDesc o ⟧ X → ⟦ D ⟧ X
forgetNT `0 (() , _)
forgetNT (x⁺ ⊕ xs⁺) (zero , v) = 0 , conForgetNT x⁺ v
forgetNT (x⁺ ⊕ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

forgetAlg : ∀{#c}{D : DatDesc #c} (o : DatOrn D) →
            DatAlg (ornToDesc o) (μ D)
forgetAlg o = ⟨_⟩ ∘ forgetNT o

forget : ∀{#c}{D : DatDesc #c} (o : DatOrn D) →
         μ (ornToDesc o) → μ D
forget o = fold (forgetAlg o)
\end{code}\end{codelst}

\begin{example}
Let us take a look at the ornamental algebra for the |nat→list|
ornament. The |forget| function for this ornament should take a list
to a natural. More precisely, applying |forget| to |nat→list| for a
given parameter |A| results in a function which takes a |μ (listDesc
A)| to a |μ natDesc|. Each nil is taken to a zero and cons is taken to
a suc, the extra elements of type |A| which were introduced by the
ornament are forgotten. This happens to result in exactly the length
of the list, so we might define a length function as |forget nat→list|:

\begin{code}
`length : ∀{A} → μ (listDesc A) → μ natDesc
`length = forget nat→list

test-length : `length ("one" `∷ "two" `∷ `[]) ≡ `suc (`suc `zero)
test-length = refl
\end{code}
\end{example}

\begin{example}
  The |give-K| ornament is useful if one wishes to specialise a
  datatype, instantiating some argument to a particular value. For
  instance, one could write an ornament for lists of naturals which
  instantiates each element to the number |7|. This ornament happens
  to result in the description of naturals.

\begin{code}
list→listof7s : DatOrn (listDesc Nat)
list→listof7s = ι ⊕ give-K 7 (rec-⊗ ι) ⊕ `0

test-list→listof7s : ornToDesc list→listof7s ≡ natDesc
test-list→listof7s = refl
\end{code}

It seems odd that we can have ornaments which go from naturals to
lists, and ornaments form lists to naturals as well. The point here is
that within the context of the |list→listof7s| ornament that natural
has a very particular meaning, namely the length of the list. This becomes
obvious when we |forget| the ornament. By passing the number two, we get
a list of length two where the values for the elements are provided by
the ornament itself.

\begin{code}
forget-listof7s : forget list→listof7s (`suc (`suc `zero)) ≡ (7 `∷ 7 `∷ `[])
forget-listof7s = refl
\end{code}

So in fact, we are replicating |7|s here. We can generalise the
ornament a bit to get a function which repeats a given element a given
number of times:

\begin{code}
`replicate : ∀{A} → A → μ natDesc → μ (listDesc A)
`replicate x = forget (ι ⊕ give-K x (rec-⊗ ι) ⊕ `0)
\end{code}

Interestingly, the |`length| function which was obtained by the
ornamental algebra of |nat→list| is the inverse of this |`replicate|
function which we got with the ornamental algebra of
|list→listof7s|. This is not a coincidence. The |nat→list| ornament
(|ι ⊕ A +⊗ rec-⊗ ι ⊕ `0|) inserts exactly the argument which was
removed by the |list→listof7s| ornament (|ι ⊕ give-K 7 (rec-⊗ ι) ⊕
`0|), while keeping the rest of the description the same.  If we say
that an ornament |o₂| is an inverse of the ornament |o₁| iff |forget
o₂| is the inverse of |forget o₁|, we could say that |nat→list| is the
inverse ornament of |list→listof7s|.
\end{example}


\section{Discussion}\label{sec:sop-discussion}

In this chapter we have presented a universe of descriptions for
simple datatypes. At the root they are ordinary sum-of-products
descriptions which support recursion using fixpoints. Although we did
represent types with datatype parameters, the parameter abstractions
were always done externally and the descriptions are not aware of any
differences between datatype parameters and other arguments. The
Regular \cite{noort08} datatype-generic programming library for
Haskell has a similar scope where parameters and indices are not
supported. An Agda formalisation of the Regular library is presented
by Magalhães and Löh \cite{magalhaes12}. The codes for the universe
they use are shown in \fref{lst:sop-regular-codes}. There are codes
for units, recursive positions, sums and products. The decoding
function |⟦_⟧| and the fixpoint datatype |μ| are similar to those in
this chapter.

\begin{codelst}{Codes for a universe of regular types}{sop-regular-codes}\begin{code}
data Code : Set where
  ι : Code
  rec : Code
  _⊕_ : (F G : Code) → Code
  _⊗_ : (F G : Code) → Code
\end{code}\end{codelst}

The types which can be represented with the descriptions in this
chapter are limited to the \emph{regular} types, those which can be
defined using the units, sums, products and the fixpoints |μ| of this
chapter \cite{noort08}. Regular types (also known as context-free
types \cite{altenkirch06}) do not allow nested datatypes \cite{bird98}
or mutual recursion. A regular type does not necessarily correspond to
one single datatype though. For instance, list of booleans is a
regular type which could be encoded as a regular type as |A ⊗ (ι ⊕
ι)|. To define that type using Agda datatypes would however require
multiple datatypes, namely the |List| and |Bool| types.

With regards to the ultimate goal of using our descriptions to
accurately represent and even define Agda datatypes, we need to impose
some restrictions on our descriptions which libraries like Regular do
not need. We have to make sure that every description corresponds to
exactly one Agda datatype. An Agda datatype is always a sum of
products, where each term of the top-level sum corresponds to a
constructor and the factors of those terms correspond to constructor
arguments. The split between |ConDesc|s and |DatDesc|s enforces this
structure.

Our descriptions also differ from those in
\fref{lst:sop-regular-codes} in that ours have a list-like structure
where |ι| and |_`0_| function as nil and |_⊗_|, |rec-⊗_| and |_⊕_| as
cons. This has two benefits: It ensures that every description has one
canonical representation and it is easier to work with, both in
construction and consumption.

\subsection{Σ-descriptions}

The descriptions we have seen all have sums and products using |_⊕_|
and |_⊗_|. In dependently typed languages we have Σ-types, which can
be used to encode both sums and products \cite{chapman10}. Some of the
work on ornaments which we will be referring to uses descriptions with
Σ's, so we will take a look at them. To start with, we define a
universe of descriptions and their decoding in \fref{lst:sop-Σdesc}.

\begin{codelst}{Universe of Σ-descriptions}{sop-Σdesc}\begin{code}
data DescΣ : Set₁ where
  ι : DescΣ
  σ : (S : Set) → (xs : S → DescΣ) → DescΣ
  rec-×_ : (xs : DescΣ) → DescΣ

⟦_⟧DescΣ : DescΣ → Set → Set
⟦ ι ⟧DescΣ X = ⊤
⟦ σ S xs ⟧DescΣ X = Σ S λ s → ⟦ xs s ⟧DescΣ X
⟦ rec-× xs ⟧DescΣ X = X × ⟦ xs ⟧DescΣ X

data μΣ (D : DescΣ) : Set where
  ⟨_⟩ : ⟦ D ⟧DescΣ (μΣ D) → μΣ D
\end{code}\end{codelst}

The |σ| description is used to describe Σ-types, the rest should be
familiar (it is the same as our descriptions).  The following
description of the |Either| type illustrates quite well how a |σ| can
mean different things. The |Either| type has two constructors; the
choice between them is made by asking for a |Fin 2| in the outer
|σ|, the pattern-matching lambda then picks the description of a
constructor based on the |Fin 2| value. The top-level |σ| thus works
as a sum of two constructors. The inner |σ|'s
function like |_⊗_|; in the first constructor an |A| is asked for, in
addition to the rest of the description for that constructor where the
value |a : A| may be used.

\begin{code}
eitherDescΣ : (A B : Set) → DescΣ
eitherDescΣ A B = σ (Fin 2) λ
  { zero → σ A λ a → ι
  ; (suc zero) → σ B λ b → ι
  ; (suc (suc ())) }

eitherDescΣ-left : ∀{A B} → A → μΣ (eitherDescΣ A B)
eitherDescΣ-left x = ⟨ 0 , x , tt ⟩
eitherDescΣ-right : ∀{A B} → B → μΣ (eitherDescΣ A B)
eitherDescΣ-right x = ⟨ 1 , x , tt ⟩
\end{code}

The types which are encoded by our universe are a subset of those
which can be encoded by Σ-descriptions. \Fref{tab:sop-Σ-comparison}
shows how a |ConDesc| or |DatDesc| can be translated into a |DescΣ|
with an equivalent semantics. Note how |DatDesc| needs multiple
constructors to encode a sum where |DescΣ| uses just one |σ|. That is
why we need the |lookupCtor| function to define the decoding and
|DescΣ| does not.

\begin{table}[t]
\centering
\begin{tabular}{ l l l }
|ConDesc|/|DatDesc| & |DescΣ| & |⟦_⟧| \\ \hline
|ι| & |ι| & |⊤| \\
|S ⊗ xs| & |σ S λ _ → xs| & |S × ⟦ xs ⟧ X| \\
|rec-⊗ xs| & |rec-× xs| & |X × ⟦ xs ⟧ X| \\
|x_0 ⊕ x_1 ⊕ ⋯ ⊕ x_n-1 ⊕ `0| & |σ (Fin n) λ k → x_k| &
|Σ (Fin n) λ k → ⟦ x_k ⟧ X| \\
\end{tabular}
\caption{Descriptions and their |DescΣ| counterparts}
\label{tab:sop-Σ-comparison}
\end{table}

In \fref{lst:sop-Σorn} we define ornaments for copying of |ι|, |σ| and
|rec-×_| and for insertion and deletion of |σ|'s. This is similar to
those defined by Dagand and McBride \cite{dagand14-transporting}. Note
that |insert-σ| is similar to our |_+⊗_| ornament and |delete-σ| is
similar to |give-K|.

\begin{codelst}{Ornaments on Σ-descriptions}{sop-Σorn}\begin{code}
data OrnΣ : (D : DescΣ) → Set₁ where
  ι : OrnΣ ι
  σ : (S : Set) → ∀{xs} (xs⁺ : (s : S) → OrnΣ (xs s)) → OrnΣ (σ S xs)
  rec-×_ : ∀{xs} (xs⁺ : OrnΣ xs) → OrnΣ (rec-× xs)
  insert-σ : (S : Set) → ∀{xs} → (xs⁺ : S → OrnΣ xs) → OrnΣ xs
  delete-σ : ∀{S xs} → (s : S) → (xs⁺ : OrnΣ (xs s)) → OrnΣ (σ S xs)

ornToDescΣ : ∀{D} → OrnΣ D → DescΣ
ornToDescΣ ι = ι
ornToDescΣ (σ S xs⁺) = σ S (λ s → ornToDescΣ (xs⁺ s))
ornToDescΣ (rec-× xs⁺) = rec-× (ornToDescΣ xs⁺)
ornToDescΣ (insert-σ S xs⁺) = σ S (λ s → ornToDescΣ (xs⁺ s))
ornToDescΣ (delete-σ s xs⁺) = ornToDescΣ xs⁺
\end{code}\end{codelst}

As a quick example, we can now define descriptions of naturals and
the ornamentation from naturals to lists. The ornament inserts a new
|σ| in the description, and results in a description which can
describe lists.

\begin{code}
natDescΣ : DescΣ
natDescΣ = σ (Fin 2) λ
  { zero → ι
  ; (suc zero) → rec-× ι
  ; (suc (suc ())) }

nat→listΣ : (A : Set) → OrnΣ natDescΣ
nat→listΣ A = σ (Fin 2) λ
  { zero → ι
  ; (suc zero) → insert-σ A λ a → rec-× ι
  ; (suc (suc ())) }
\end{code}

Σ-descriptions are a way to describe sums of products using a very
small number of components. All the types which can be encoded in our
universe or in the regular types universe of
\fref{lst:sop-regular-codes} can be encoded with Σ-descriptions
too. Additionally, because the tail description |xs| of a |σ| is a
function of type |S → DescΣ| the full computational power of functions
can be used. This results in the ability to encode rather exotic
types. For instance a type which takes a number |n| and then an |n|
amount of |Bool|'s: \todo{Remove this example? Doesn't really add
  much..}

\begin{code}
boolsDescΣ : DescΣ
boolsDescΣ = σ Nat rest
  where rest : Nat → DescΣ
        rest zero = ι
        rest (suc n) = σ Bool λ _ → rest n

boolsDescΣ-example : μΣ boolsDescΣ
boolsDescΣ-example = ⟨ 3 , true , false , true , tt ⟩
\end{code}

We can not use Σ-descriptions for our purposes, because they allow
many types which do not correspond to Agda datatypes. However, their
simplicity does provide a good vantage point to consider the more
theoretical aspects of ornaments. While working with complicated
descriptions like ours, it is often enlightening to take a step back
and consider what things would look like with Σ-descriptions.

\subsection{Finding the right ornaments}

The ornaments in this chapter where presented without much
explanation, but there are in fact some choices to make here. To
figure out what the ornaments are for a particular set of
descriptions, one first has to answer an essential question: When can
a transformation from one description to another be called an
ornament? We already know that each ornament comes with a |forget|
function. Instead of relying on vague notions like 'being more
informative', we can make the requirement quite formal: a
transformation from one description to another is an ornament
\emph{iff} it comes with a |forget| function. This is the one and only
requirement, so by defining the |forget| function we have shown that
our ornaments can really be called ornaments.

The ornaments we use, defined in \fref{lst:sop-ornaments}, are mostly
adapted from the ornaments for Σ-descriptions in
\fref{lst:sop-Σorn}. \Fref{tab:sop-ornΣ-comparison} shows how they
relate to each other.  The exact meaning of each row is as follows:
Given a description |D| and a Σ-description |DΣ| which both decode to
\emph{Original PF}, the application of |o| to |D| and |oΣ| to |DΣ|
both result in descriptions which decode to \emph{Ornamented PF}. We
already knew that our descriptions and their corresponding
Σ-descriptions had the same underlying pattern functors
(\fref{tab:sop-Σ-comparison}), and now it turns out that the ornaments
on our descriptions and the corresponding ornaments on Σ-descriptions
perform the same operation on the underlying pattern functors as
well. Note that we overloaded the notation |⟦ o ⟧| once more, such
that when it is applied to ornaments it can mean |⟦ ornToDesc o ⟧| or
|⟦ ornToDescΣ o ⟧|.

\begin{table}
\centering
\begin{tabular*}{\textwidth}{@@{\extracolsep{\fill} } l l l l }
\multicolumn{2}{ c }{Ornament from original PF to ornamented PF} &
Original PF & Ornamented PF \\
\cline{1-2}
|o : Con/DatOrn D| & |oΣ : OrnΣ DΣ| &
|⟦ D ⟧| and |⟦ DΣ ⟧| & |⟦ o ⟧| and |⟦ oΣ ⟧| \\
\hline
|ι| & |ι| & |⊤| & |⊤| \\
|-⊗ xs⁺| & |σ S λ _ → xs⁺| & |S × ⟦ xs ⟧ X| & |S × ⟦ xs⁺ ⟧ X| \\
|S +⊗ xs⁺| & |insert-σ S λ _ → xs⁺| & |⟦ xs ⟧ X| & |S × ⟦ xs⁺ ⟧ X| \\
|give-K s xs⁺| & |delete-σ s xs⁺| & |S × ⟦ xs ⟧ X| & |⟦ xs⁺ ⟧ X| \\
|rec-⊗ xs⁺| & |rec-× xs⁺| & |X × ⟦ xs ⟧ X| & |X × ⟦ xs⁺ ⟧ X| \\
|rec-+⊗ xs⁺| & - & |⟦ xs ⟧ X| & |X × ⟦ xs⁺ ⟧ X| \\
(|give-rec|?) & - &
  |X × ⟦ xs⁺ ⟧ X| & |⟦ xs⁺ ⟧ X| \\
|x_0⁺ ⊕ x_1⁺ ⊕ ⋯ ⊕ `0| & |σ (Fin n) λ k → x_k⁺| &
  |Σ (Fin n) λ k| & |Σ (Fin n) λ k| \\
 & & \hfill |→ ⟦ x_k ⟧ X| & \hfill |→ ⟦ x_k⁺ ⟧ X| \\
% - & insert-σ (Fin n) λ k → x_k⁺ 
\end{tabular*}
\caption{Ornaments and their |OrnΣ| counterparts}
\label{tab:sop-ornΣ-comparison}
\end{table}

With the exception of |rec-+⊗_|, every ornament of ours has a |OrnΣ|
counterpart. We included |rec-+⊗_| because we can define the
ornamental algebra for it, and there is no particular reason not to
use it. One would then also expect an ornament which deletes recursive
arguments. Similar to |give-K|, the ornament would require a default
value to be able reconstruct the right value in the ornamental
algebra. The type of this value is however not known within the
ornament declaration so we can not define it as far as we know.

\begin{code}
-- Constructor for |ConOrn|
  give-rec : ∀{xs} → ? → (xs⁺ : ConOrn xs) → ConOrn (rec-⊗ xs)
\end{code}

There are still some ornaments missing which we did have for
Σ-descriptions. Because a chain of constructors |x_0 ⊕ x_1 ⊕ ⋯ ⊕ `0|
is similar to |σ (Fin n) λ k → x_k|, we would expect the ornaments
|insert-σ| and |delete-σ| to have a counterpart in our ornaments. The
main reason why we do not have those is because an equivalent ornament
would have to insert or delete the whole constructor chain. The
deletion of the chain would mean one ends up with a single constructor
and the insertion would require a single constructor to start
with. Our ornaments have to go from |DatDesc| to |DatDesc|, so these
operations are both not valid.

Dagand and McBride \cite{dagand14-transporting} do use |insert-σ| to
insert a constructor choice quite often though, while still keeping
descriptions which make sense. The trick is to always let an
|insert-σ| be followed by |delete-σ|'s. For instance, we can define
the |swapnatΣ| ornament which swaps the constructors of |natDescΣ|. The
|insert-σ (Fin 2)| says there are going to be two constructors and for
each constructor we have to provide an ornament on the original
|natDescΣ|. In the first constructor, |delete-σ 1| means that we
choose the second constructor of |natDescΣ|; the |rec-× ι| does
nothing but copying.

\begin{code}
swapnatΣ : OrnΣ natDescΣ
swapnatΣ = insert-σ (Fin 2) λ
  { zero → delete-σ 1 (rec-× ι)
  ; (suc zero) → delete-σ 0 ι
  ; (suc (suc ())) }
\end{code}

An |insert-σ (Fin n)| on the top-level is fine if the first thing we
do for each constructor is to pick one of the constructors of the
original type using |delete-σ|. We \emph{can} implement a |recons|
ornament on |DatDesc| which has this behavior. The first argument
|#c⁺| is the number of constructors we want the ornamented type to
have (while |#c| is the number of constructors of the original
type). For each of the new constructors, i.e. for each value of |Fin
#c⁺|, two things have to be provided: A value |k| of type |Fin #c| to
pick a constructor of the original type and an ornament on that
constructor. The |recons| constructor for |DatOrn| looks like this:

\begin{code}
  recons :
    ∀ #c⁺ {#c} {D : DatDesc #c} →
    (f : (k⁺ : Fin #c⁺) → (Σ (Fin #c) λ k → ConOrn (lookupCtor D k))) →
    DatOrn {#c} D
\end{code}

With it, we can write the |swapnat| ornament for our universe of
descriptions. By comparing |swapnat| with |swapnatΣ| we see that, as
expected, the
user still has to provide all of the same information with the
exception of the |insert-σ| and |delete-σ|'s.

\begin{code}
swapnat : DatOrn natDesc
swapnat = recons 2 λ
  { zero → 1 , rec-⊗ ι
  ; (suc zero) → 0 , ι
  ; (suc (suc ())) }
\end{code}

The |recons| ornament is feasible to implement and makes sense in
practice, as indicated by the use of the pattern of |insert-σ| and
|delete-σ|'s by Dagand and McBride. We do not implement them for our
descriptions in the following chapters for entirely pragmatic
reasons. The implementation is hard to get right, even for this simple
universe. It also complicates other parts of the code because we can
not assume that an ornament keeps the same number of
constructors. Just to prove our point and for completeness, the
changes needed to support |recons| in |ornToDesc| and the ornamental
algebra are listed in \fref{lst:sop-recons-changes}. The functions
|tabulateCtors| and |lookup-tabulate| provide some standard |Vec|
functionality for |DatDesc|. The type of |ornToDesc| has to support
changes to the number of constructors, which is calculated using
|ornToDesc-#c|. Finally the case for |recons| has to be added to |forgetNT| to
complete the implementation of |forget|.

\begin{codelst}{Changes required to support |recons|}{sop-recons-changes}\begin{code}
tabulateCtors : ∀{n} → (Fin n → ConDesc) → DatDesc n
tabulateCtors {zero} f = `0
tabulateCtors {suc n} f = f 0 ⊕ tabulateCtors (f ∘ suc)

lookup-tabulate : ∀{#c}(f : Fin #c → ConDesc) i →
                  lookupCtor (tabulateCtors f) i ≡ f i
lookup-tabulate f zero = refl
lookup-tabulate f (suc i) = lookup-tabulate (f ∘ suc) i

ornToDesc-#c : ∀{#c}{D : DatDesc #c} → DatOrn D → Nat
ornToDesc-#c `0 = 0
ornToDesc-#c (_ ⊕ xs⁺) = suc (ornToDesc-#c xs⁺)
ornToDesc-#c (recons n _) = n

-- The type of |ornToDesc| changes
ornToDesc : ∀{#c}{D : DatDesc #c} →
  (o : DatOrn D) → DatDesc (ornToDesc-#c o)

-- Case for |recons| in |ornToDesc|
ornToDesc (recons _ xs⁺) = tabulateCtors (conOrnToDesc ∘ snd ∘ xs⁺)

-- Case for |recons| in |forgetNT|
forgetNT (recons _ f) {X} (c , v) =
  let v′ = transport (λ a → ⟦_⟧ a X) (lookup-tabulate _ c) v in
  fst (f c) , conForgetNT (snd (f c)) v′

\end{code}\end{codelst}