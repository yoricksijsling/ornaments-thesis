%include thesis.fmt

\chapter{Discussion}\label{chap:discussion}

The structure of our descriptions matches closely with the structure
of actual datatype declarations. We have chosen to split them up into
constructor descriptions and datatype descriptions, and to have a
first-order structure to determine which arguments each constructor
has. Functions are only allowed within parts where arbitrary terms
could occur in real datatypes. Our descriptions have strict control
over what can and what can not be influenced by the context.

Descriptions encode indexed functors that are of the form |(I → Set) →
(O → Set)|. There are many ways to encode indexed functors, including
ways that build on the Σ-descriptions of \cref{sec:sop-Σdesc}. Indexed
containers\cite{altenkirch09} can also be used, but for our purposes
they have the same problems as Σ-descriptions: They can be used to
define a lot of exotic types that do not correspond to an Agda
datatype. Indexed Σ-descriptions and, even more so, indexed containers
serve well as \emph{semantical} models of inductive families, but they
do not provide an accurate \emph{syntactical} representation of Agda
datatypes.


\section{Explicit parameter use}\label{sec:discussion-params}

In our descriptions, starting with those in \cref{chap:simple}, 'types
within a context' were represented with a function of type |⟦ Γ ⟧ →
Set|. This allows any type to be represented and the type may depend
on a local environment. While this is a very powerful approach if one
only cares about representing types, it is not very helpful when the
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
descriptions of \cref{chap:extended}, these functions would have the
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
multiple parameters. \Cref{lst:disc-multipolyp} defines the
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
\end{code}
\begin{code}
treeDesc : Desc (ε ▷′ Set)
treeDesc = par top′ ⊕ rec ⊗ rec

tree-to : ∀{A} → Tree A → μ treeDesc (tt , A)
tree-to (leaf v) = ⟨ left v ⟩
tree-to (node xs ys) = ⟨ right (tree-to xs , tree-to ys) ⟩
\end{code}

So far so good, we can do what we already could in
\cref{chap:extended}. To show that we have indeed made progress, we
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
  descriptions of \cref{sec:ext-separateparams}, where the parameters
  are separated from internal contexts, do not have this problem.
\item The possibility of false negatives. If one introduces a new
  constructor for parameter argumenst while keeping the old |_⊗_|
  constructor with the |⟦ Γ ⟧ → Set| argument, both can be used to
  encode the use of a parameter. One can then still not say with
  certainty that an argument is \emph{not} the simple use of a
  parameter.
\end{itemize}

When the ability to describe as many types as possible is less
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


\section{Induction-recursion and strict positivity}\label{sec:discussion-ri}

Our descriptions are able to describe a practical subset of the
\emph{inductive types}. Dybjer and Setzer \cite{dybjer99} describe
\emph{ordinary inductive definitions} of types with a finite number of
constructors:

\begin{code}
conᵢ : Φᵢ U → U
\end{code}

The |Φᵢ| are strictly positive functors. If dependent types are
allowed, strictly positive functors can be constructed by a number of
rules (according to Dybjer and Setzer):

\begin{itemize}
\item |nil|: The constant functor |Φ X = ⊤| is strictly positive.
\item |nonind|: If |A| is a type and |Ψₓ| is a strictly positive
  functor depending on |(a : A)|, then |Φ X = Σ A λ a → Ψₐ X| is
  strictly positive.
\item |ind|: If |Ψ| is strictly positive, then |Φ X = X × Ψ X| is
  strictly positive.
\end{itemize}

% We implement inductive types
The rules |nil|, |nonind| and |ind| correspond exactly to the
semantics of |ι|, |σ| and |rec-×_| of the Σ-descriptions in
\cref{lst:sop-Σdesc} on \cpageref{lst:sop-Σdesc}, while the
introduction rule |conᵢ : Φᵢ U → U| corresponds to the constructor of
the fixpoint datatype |μΣ|. We have shown in
\cref{tab:sop-Σ-comparison} (\cref{sec:sop-Σdesc}) that our
|ConDesc|/|DatDesc| universe of that chapter can describe a subset of
those Σ-descriptions, so by the rules stated above this means that
that universe describes a subset of the ordinary inductive types.

% Inductive families
In later chapters we have extended the universe in several ways, but
the same logic still holds. One can confirm that the semantics for
families of datatypes in \cref{lst:ext-semantics} can be generated
with similar rules as above, though slightly modified to allow
indices. The |ConDesc|/|DatDesc| universes with indices describe
inductive families.

% No depending on inductive arguments
Note that the |ind| rule does not allow later arguments to depend on
the value of an inductive argument. So within a datatype |D|, an
arguments in a constructor can not depend on earlier arguments of type
|D|. Our |ConDesc|/|DatDesc| universes reflect this fact by not
including the |S| of a |rec S × xs| in the context for |xs|. We know
that Agda datatypes do not have such restrictions---They are not
just inductive types.

\emph{Inductive-recursive} types are a generalisation of inductive
types, where a simultaneously defined recursive function of type |D →
...| can be used within the definition of the type |D|. A simple
example is our |Cx| type in \cref{lst:simple-cx} on
\cpageref{lst:simple-cx}, which is mutually defined with
|⟦_⟧Cx|. Dybjer and Setzer \cite{dybjer99} have given an
axiomatisation of inductive-recursive types that can be implemented in
Agda easily.

Compared to inductive types, the pattern functors of
inductive-recursive types can use an extra argument |T| that
represents a recursively defined function\footnote{Actually, as Dybjer
  and Setzer note, the functors are not really functors anymore in the
  category theory sense of the word.}. Now in the case of an inductive
argument |a|, later arguments can depend on |T a| (not on \emph{just}
|a|). For example; when describing the type |Cx| the function |T|
would represent |⟦_⟧Cx|. When |(Γ : Cx)| is an (inductive) argument,
the rest of the arguments could depend on |⟦ Γ ⟧Cx|. This is
sufficient to encode the |_▷_| constructor, which is of type |(Γ : Cx)
→ (⟦ Γ ⟧Cx → Set) → Cx|.

Separately from inductive-recursive types, ordinary inductive types
can also be extended in another way--To \emph{generalised} inductive
types. Generalised inductive types are the same as ordinary inductive
types, but with the inclusion of an inductive premise in the |ind|
rule, giving the following rule:

\begin{itemize}
\item |ind|: If |Ψ| is strictly positive and |A| is a type, then |Φ X
  = (A → X) × Ψ X| is srictly positive. If one instantiates |A| to
  |⊤|, one obtains the ordinary inductive types (up to isomorphism).
\end{itemize}

To summarise, there are three ways to expand on ordinary inductive
types:

\begin{itemize}
\item By adding indices, so \emph{inductive families} can be
  described. This was done for our universe in \cref{chap:extended}.
\item By allowing inductive premises, to get \emph{generalised}
  inductive types.
\item By passing a recursive function to the pattern functors, to
  implement \emph{inductive-recursive} types.
\end{itemize}

The |ConDesc|/|DatDesc| universe has not been adapted to implement the
latter two, but this may well be possible. Dybjer and Setzer have
presented \emph{indexed inductive-recursive} types\cite{dybjer01},
combining the combination of these three expansions. Indexed
inductive-recursive types are a good approximation of the datatypes
that are implemented by Agda. It would be interesting to see if our
universes, ornaments, and generic programming framework could be
rebuilt with indexed inductive-recursive types as their foundation.


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

