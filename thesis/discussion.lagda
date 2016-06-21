%include thesis.fmt

\chapter{Discussion}\label{chap:discussion}

The structure of our descriptions match closely with the structure of
actual datatype declarations. Only those parts which can contain
arbitrary terms are represented as higher order arguments in our
descriptions.

\section{Detecting parameter use}

In our descriptions, starting with \fref{chap:simple}, 'types within a
context' were represented with a function of type |⟦ Γ ⟧ → Set|. This
allows any type to be represented and the type may depend on a local
environment. While this is a very powerful approach if one only cares
about representing types, it is not very helpful when the
representation needs to be \emph{inspected}. For instance, one can not
decide whether a given term uses a certain parameter. More precisely,
the following definition of |isTop| can not be completed. For an
arbitrary |S| of type |⟦ ε ▷₁′ Set ⟧ → Set|, we can neither prove that
it is |top| or that it is not |top|.

\begin{code}
data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

isTop : (S : ⟦ ε ▷₁′ Set ⟧ → Set) → Dec (∀ γ → S γ ≡ top γ)
isTop S = ?0
\end{code}

This quickly becomes a problem when writing generic functions. A
common function in generic programming frameworks is |flatten|; it
takes a value of a type with a type parameter |A|, and converts it
into a |List A|. Another is the parametric map function |pmap| which
maps a function |(f : A → B)| over elements in a structure. With the
descriptions of \fref{chap:extended}, these functions would have the
following type:

\begin{code}
flatten : ∀{#c} (D : DatDesc ε (ε ▷₁′ Set) #c) →
  ∀{A} → μ D (tt , A) tt → List A
pmap : ∀{#c} (D : DatDesc ε (ε ▷₁′ Set) #c) →
  ∀{A B} → (f : A → B) → μ D (tt , A) tt → μ D (tt , B) tt
\end{code}

The implementation of both |flatten| and |pmap| is impossible with our
descriptions, because it can not be decided where parameters are being
used. Other generic programming frameworks often do not have this
problem, because they have a separate description for parameter
use. For instance, a subset of the universe of PolyP (where a single
parameter is allowed) can be encoded in Agda as follows
\cite{jansson97,magalhaes12}:

\begin{code}
    data PolyPDesc : Set where
      ι : PolyPDesc
      rec : PolyPDesc
      par : PolyPDesc
      _⊕_ : (F G : PolyPDesc) → PolyPDesc
      _⊗_ : (F G : PolyPDesc) → PolyPDesc
\end{code}

The decoding for this universe is of type |PolyPDesc → (P : Set) → (X
: Set) → Set|, where the decoding of |par| results in the parameter
type |P|. With simple pattern matching, the usage of the parameter can
be detected. This same idea can be made to work for multiple
parameters in a |Cx|. We use |Γ ∋Set| as proofs that a |Set| is
specified in the context, and |⟦_⟧∋Set| to lookup the type (a value of
type |Set|) in an environment |γ|. Note that |_∋Set| and |⟦_⟧∋Set| are
specifically meant to lookup \emph{types} in the environment. The same
can be done to lookup values in the environment, but other definitions
are needed \cite{mcbride10}.

\begin{code}
data _∋Set : (Γ : Cx) → Set₁ where
  top′ : ∀{Γ} → (Γ ▷′ Set) ∋Set
  pop′ : ∀{Γ S} → Γ ∋Set → (Γ ▷ S) ∋Set

⟦_⟧∋Set : ∀{Γ} → Γ ∋Set → (γ : ⟦ Γ ⟧) → Set
⟦ top′ ⟧∋Set (γ , t) = t
⟦ pop′ i ⟧∋Set (γ , s) = ⟦ i ⟧∋Set γ
\end{code}

With these definitions, the PolyP universe can be modified to support
multiple parameters. \Fref{lst:disc-multipolyp} defines the
descriptions and semantics of the new universe. The semantics are
mostly business as usual---the parameters are decoded with |⟦_⟧∋Set|.

\begin{codelst}{Descriptions with parameter lookup}{disc-multipolyp}\begin{code}
data Desc (Γ : Cx) : Set₁ where
  ι : Desc Γ
  rec : Desc Γ
  par : (i : Γ ∋Set) → Desc Γ
  _⊕_ : Desc Γ → Desc Γ → Desc Γ
  _⊗_ : Desc Γ → Desc Γ → Desc Γ

⟦_⟧desc : ∀{Γ} → Desc Γ → ⟦ Γ ⟧Cx → Set → Set
⟦ ι ⟧desc γ X = ⊤
⟦ rec ⟧desc γ X = X
⟦ par i ⟧desc γ X = ⟦ i ⟧∋Set γ
⟦ A ⊕ B ⟧desc γ X = Either (⟦ A ⟧desc γ X) (⟦ B ⟧desc γ X)
⟦ A ⊗ B ⟧desc γ X = ⟦ A ⟧desc γ X × ⟦ B ⟧desc γ X

data μ {Γ}(D : Desc Γ) (γ : ⟦ Γ ⟧) : Set where
  ⟨_⟩ : ⟦ D ⟧desc γ (μ D γ) → μ D γ
\end{code}\end{codelst}

A binary tree type, with data of type |A| in the leaves, is defined as
|Tree A|. The new universe can describe this type, where |par top′| is
used to refer to the parameter. Note that constructors in this
universe do not have to be terminated with a |ι|. We show that the
definition makes sense by defining the |tree-to| function, to convert
real trees into represented trees.

\begin{code}
data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

treeDesc : Desc (ε ▷′ Set)
treeDesc = par top′ ⊕ rec ⊗ rec

tree-to : ∀{A} → Tree A → μ treeDesc (tt , A)
tree-to (leaf v) = ⟨ left v ⟩
tree-to (node xs ys) = ⟨ right (tree-to xs , tree-to ys) ⟩
\end{code}

So far so good, we can do what we already could in
\fref{chap:extended}. To show that we have indeed made progress, we
will define the |flatten| function, for which parameter use needs to
be recognised. Using straightforward definitions for |Alg| and |fold|,
a |flattenAlg| algebra can be defined which works for any
description. Notice how we can simply pattern match on |par top′| to
extract the value of type |A|.

\begin{code}
flattenAlg : ∀{Γ} (D : Desc (Γ ▷′ Set)) →
  ∀{γ A} → Alg D (γ , A) (List A)
flattenAlg ι tt = []
flattenAlg rec x = x
flattenAlg (par top′) x = [ x ]
flattenAlg (par _) x = []
flattenAlg (A ⊕ B) (left x) = flattenAlg A x
flattenAlg (A ⊕ B) (right x) = flattenAlg B x
flattenAlg (A ⊗ B) (x , y) = flattenAlg A x ++ flattenAlg B y
\end{code}

Finally, the flatten algebra can be folded over a tree to retrieve a
list of all the elements:

\begin{code}
tree-example : Tree Nat
tree-example = node (leaf 7) (node (node (leaf 5) (leaf 3)) (leaf 1))

test-flatten : fold (flattenAlg treeDesc) (tree-to tree-example)
  ≡ 7 ∷ 5 ∷ 3 ∷ 1 ∷ []
test-flatten = refl
\end{code}

In summary, it is possible to explicitly encode parameter references
in descriptions when the parameters are declared with a |Cx|. Of
course, this would be nice to integrate into our descriptions of
\ref{chap:extended} or \ref{chap:named}. There are two things holding
us back:

\begin{itemize}
\item With the simple universe in this section the use of the last
  parameter \emph{always} looks like |par top′|, so a simple pattern
  match suffices. In our descriptions, contexts do not remain
  constant but depend on where in a constructor we are. The
  descriptions of \fref{sec:ext-separateparams}, where the parameters
  are separated from internal contexts, do not have this problem.
\item The possibility of false negatives. If one introduces a new
  constructor for parameter argumenst while keeping the old |_⊗_|
  constructor with the |⟦ Γ ⟧ → Set| argument, both can be used to
  encode the use of a parameter. One can then still not say with
  certainty that an argument is \emph{not} the simple use of a
  parameter.
\end{itemize}

When the ability to describe as many types as possible is not
important, one could get rid of the old |⟦ Γ ⟧ → Set| arguments
altogether. Instead, a language of types could be used like
McBride's \cite{mcbride10}. McBride defines a type-is-representable
predicate |_⋆_| in the style of Crary et al \cite{crary98}. The
predicate ensures that types are only built using the language as
defined in the constructors of |_⋆_|. It is indexed by a |⟦ Γ ⟧ → Set|
function, telling us what the expected behavior is. As an example, we
define the type language to have three types: natural numbers, sets,
and types from the context.

\begin{code}
  data _⋆_ (Γ : Cx) : (⟦ Γ ⟧ → Set) → Set₁ where
    `Nat : Γ ⋆ const Nat
    `Set : Γ ⋆ const Set
    `TypeVar : (i : Γ ∋Set) → Γ ⋆ ⟦ i ⟧∋Set
\end{code}

Limited experimentation shows that the |⟦ Γ ⟧ → Set| function in the
|_⊗_| constructor of our descriptions can be replaced by |Γ ⋆ S|. So
the constructor type is changed from |(S : ⟦ Γ ⟧ → Set) → ...| to |{S
  : ⟦ Γ ⟧ → Set} → Γ ⋆ S → ...|. It remains to be seen how ornaments
will work out with such descriptions.

% The decoding for this universe is of type |Code → (P : Set) → (X :
% Set) → Set|, where the decoding of |par| results in the parameter type
% |P|. With simple pattern matching, the usage of the (single) parameter
% can be detected. This exact solution does not work for our
% descriptions, because they can have multiple (or zero)
% parameters. Within our descriptions, a better approach might be to
% replace the |(S : ⟦ Γ ⟧ → Set)| in the |_⊗_| constructor with
% something more inspectable. If 'types within a context' were
% represented as a datatype, we would be able to use pattern matching to
% detect the use of parameters. We will show that such an approach is
% feasible.

% At its core, the issue of representing dependent types is intertwined
% with representing terms with dependent types, because the full
% language of terms can be used to construct types. There is existing
% literature dealing with the internalisation of the syntax and
% semantics of type theory \cite{danielsson07}. Particularly, McBride
% \cite{mcbride10} has defined a deep embedding of a language of terms
% with dependent types within Agda where type-is-representable
% predicates are used In the style of Crary et al \cite{crary98}. This
% implementation is based on the work of McBride.

% Three definitions form the foundation of the representation of
% dependent types: the datatypes |_⋆_| and |_⊢_|, and the function
% |⟦_⟧⊢|. The datatype |Γ ⋆ T| \emph{represents types}, where the index
% |T| is the Agda interpretation of that type. This type exists within
% the context |Γ|, so |T| requires an environment of type |⟦ Γ ⟧| to
% give an actual Agda type. The datatype |Γ ⊢ Ty| \emph{represents
%   terms} of type |Ty|, where the type |Ty| is represented with a |Γ ⋆
% T|\footnote{In McBride's implementation, |_⊢_| was only indexed by |T|
%   and not by a |Γ ⋆ T|. This choice solves pattern matching issues
%   later on.}. The function |⟦_⟧⊢| interprets terms |Γ ⊢ Ty| to real
% values in Agda. If the encoded type of a term is a |Γ ⋆ T|, the term
% can be interpreted as a function |(γ : ⟦ Γ ⟧) → T γ|. The signatures
% are as follows:

% \begin{code}
% mutual
%   data _⋆_ (Γ : Cx) : (⟦ Γ ⟧ → Set) → Set₁ where
%   ...

%   data _⊢_ (Γ : Cx) : ∀{T} → (Γ ⋆ T) → Set₁ where
%   ...

%   ⟦_⟧⊢ : ∀{Γ T}{Ty : Γ ⋆ T} → Γ ⊢ Ty → (γ : ⟦ Γ ⟧) → T γ
%   ⟦_⟧⊢ = ...
% \end{code}

% As a simple example of how these definitions work, we define the |Nat|
% type within this language. The type itself is added as a constructor
% for |_⋆_|, and the index |const Nat| indicates that under every
% environment it corresponds to the Agda type |Nat|. The constructors
% for |Nat| are terms, so they are added as constructors to
% |_⊢_|. Corresponding clauses are added to the interpretation
% function. 

% \begin{code}
% -- Constructor for |_⋆_|:
%     `Nat : Γ ⋆ const Nat
% -- Constructors for |_⊢_|:
%     `zero : Γ ⊢ `Nat
%     `suc : Γ ⊢ `Nat → Γ ⊢ `Nat
% -- Cases for |⟦_⟧⊢|:
%   ⟦ `zero ⟧⊢ γ = zero
%   ⟦ `suc n ⟧⊢ γ = suc (⟦ n ⟧⊢ γ)
% \end{code}

% A term of the encoded type |`Nat| can be created using |`suc| and
% |`zero|. As expected, a value of type |ε ⊢ `Nat| can be interpreted as a |Nat|.

% \begin{code}
% `Nat-example : ε ⊢ `Nat 
% `Nat-example = `suc `zero

% interpret-`Nat-example : Nat
% interpret-`Nat-example = ⟦ `Nat-example ⟧⊢ tt
% \end{code}

% One can add many new types and terms to this embedding. For the use in
% descriptions of datatypes, we will need to lookup types in the
% context. One has to be careful that the thing being looked up is
% really a type, something of type |Set|, because normal values exist in
% the environment as well. The type |Γ ∋Set| is a proof that a context
% ∣Γ| contains a |Set|---it contains a sequence of |pop′| and |top′|s to
% indicate the position in the context. The function |⟦_⟧∋Set| takes
% such a proof and finds the specified |Set| in an environment |γ|. Note
% that |_∋Set| and |⟦_⟧∋Set| are specifically meant to lookup
% \emph{types} in the environment. The same can be done to lookup values
% in the environment, but other definitions are needed \cite{mcbride10}.

% \begin{code}
% data _∋Set : (Γ : Cx) → Set₁ where
%   top′ : ∀{Γ} → (Γ ▷′ Set) ∋Set
%   pop′ : ∀{Γ S} → Γ ∋Set → (Γ ▷ S) ∋Set

% ⟦_⟧∋Set : ∀{Γ} → Γ ∋Set → (γ : ⟦ Γ ⟧) → Set
% ⟦ top′ ⟧∋Set (γ , t) = t
% ⟦ pop′ i ⟧∋Set (γ , s) = ⟦ i ⟧∋Set γ
% \end{code}

% These definitions are used to add a new type to the embedding. The
% encoded type |`TypeVar| takes a proof that the context |Γ| contains a
% |Set|, and uses that value of type |Set| as a type.

% \begin{code}
% -- Constructor for |_⋆_|
%     `TypeVar : (i : Γ ∋Set) → Γ ⋆ ⟦ i ⟧∋Set
% \end{code}


%%%%%%%%%%%%%%%

% De |rec-⊗_| is nu ook erg beperkt, omdat het alleen directe recursieve
% calls toestaat. Dit datatype kan nu niet:

% \begin{code}
% data ListTree (A : Set) : Set where
%   node : List (ListTree A) → ListTree A
% \end{code}

% Je zou dus eigenlijk |rec-⊗_| weg willen halen en in |ArgTerm|
% opnemen. Dit is vermoedelijk ook de plek waar Π-types verwerkt kunnen
% worden. Je moet in |CxTerm| ook iets doen om negatieve occurences van
% rec te voorkomen.

% Als je een systeem zoals 'outrageous but meaningful coincidences'
% hebt, krijg je context-indexed terms. Om ook recursie en
% strict-positivity te ondersteunen wil je, net als de semantiek van
% descs, een context-indexed pattern functor opleveren.


\section{Indexed containers}

What are containers? They are entirely higher-order, while our descriptions are mostly first-order. Containers are useful when one only cares about the behavior of the datatypes (semantic vs ..).

\section{How ornaments influence the choice of descriptions}

\section{Comparison with IODesc}

\section{Williams, Dagand, Remy: Ornaments in practice}

What's the overlap, what are the differences?
