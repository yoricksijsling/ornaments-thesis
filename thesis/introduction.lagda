%include thesis.fmt

\chapter{Introduction}\label{chap:introduction}

One of the strong points of functional programming languages like
Haskell and Agda is that they allow very precise types. The type |List
A| not only tells us that it is a list, but also that every element in
the list is of type |A|. This is already a lot more static information
than many popular programming languages, and allows programmers to
adopt an 'if it type checks it works' mentality. But how precise
should we make our types? Consider the |take| function, which takes a
number of elements from the front of a list:

\begin{code}
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

take : ∀{A} → (n : Nat) → List A → List A
take zero    _        = []
take (suc n) []       = ?1
take (suc n) (x ∷ xs) = x ∷ take n xs
\end{code}

What needs to be done when the list is too short? One option is to
return a default value, like the empty list |[]|, but such behavior
may hide bugs which would be discovered otherwise. Another solution is
to change the return type to |Maybe (List A)|, so the |nothing| value
can be returned. This makes the call site responsible for error
handling. An entirely different approach is to avoid the situation by
restricting the types appropriately. Agda supports inductive families
\cite{dybjer91}, so a length index could be added to the |List|
type---resulting in the following |Vec| datatype:

\begin{code}
data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)
\end{code}

A new take function for |Vec| can be defined, which only accepts lists
of at least length |n|. Under these circumstances the problematic
clause simply disappears:

\begin{code}
takeᵥ : ∀{A m} → (n : Nat) → Vec A (n + m) → Vec A n
takeᵥ zero _ = []
takeᵥ (suc n) (x ∷ xs) = x ∷ takeᵥ n xs
\end{code}

By adding the proper indices, logic of the program can be encoded
within a datatype. One could build trees that are always sorted, trees
bounded by a minimum and maximum value, red-black trees or trees that
are always balanced. Building datatypes such that they precisely match
the logic of the program is an essential aspect of writing
correct-by-construction programs in functional programming
languages. This specialization of datatypes can however be an obstacle
to code reuse. For example; one may have defined a function to find
the first value with the property |P| in a list of natural numbers:

\begin{code}
find : List Nat → (P : Nat → Bool) → Maybe Nat
find [] P = nothing
find (x ∷ xs) P = if (P x) then (just x) else (find xs P)
\end{code}

Although we have explained |Vec|s as being a |List| with a length
index, it is \emph{defined} as an entirely separate thing. Agda has no
idea that these two are related. To search in a |Vec| of naturals, we
have to define an entirely new function:

\begin{code}
findᵥ : ∀{n} → Vec Nat n → (P : Nat → Bool) → Maybe Nat
findᵥ [] P = nothing
findᵥ (x ∷ xs) P = if (P x) then (just x) else (findᵥ xs P)
\end{code}

The same problem will occur again and again if one uses other
list-like types. We can define bounded lists that are parameterised by
a maximum value, or sorted lists that are indexed by the lowest value
in the list (so at each |_∷_| a proof can be included that the element
is at least as low as the lowest value in the tail). The
implementation of |find| for both of these can be copy-pasted:

\begin{code}
find_b : ∀{mx} → BoundedNatList mx → (P : Nat → Bool) → Maybe Nat
find_b [] P = nothing
find_b (x ∷ xs) P = if (P x) then (just x) else (find_b xs P)

find_s : ∀{l} → SortedNatList l → (P : Nat → Bool) → Maybe Nat
find_s [] P = nothing
find_s (x ∷ xs) P = if (P x) then (just x) else (find_s xs P)
\end{code}

Another example is found in the modeling of the simply-typed lambda
calculus. The datatype which describes the terms can be indexed by
their types\footnote{A |Nat| index can be used if only scoping rules
  have to be enforced.}, allowing the static enforcement of typing
rules. For this same datatype, it might also be useful to add the
evaluation result as an index to simplify reasoning about the
preservation of behavior during the mutation of terms \cite{mcbride11,
  dagand14-transporting}. The typing semantics and the evaluation
semantics both induce useful indices for the datatype. With and
without both of these indices, we can define four variants of the
datatype which can all be used under different circumstances. \todo{Is
  this paragraph still interesting?}

Maybe it would be useful if Agda knew about the relatedness of all
these different variants of datatypes. Conor McBride \cite{mcbride11}
has presented \emph{ornaments} as a way to express relations between
datatypes. Loosely speaking, one type can be said to be an ornament of
another if it contains more information in some way, for example by
the refinement with indices or the addition of data. They can be used
to express that |Vec| is an ornament of |List|, or that |List| can be
defined as an ornament on |Nat| by attaching an element of type |A|
to each |suc| constructor. Before we can start working with ornaments
we need a way to model datatypes within Agda itself.

Datatype-generic programming talks about types by using
\emph{descriptions}. These descriptions of types can take the form of
a description datatype. This is combined with a decoding function
which assigns a type to every inhabitant of the description datatype
\cite{altenkirch06}. The descriptions and decoding function together
form a \emph{universe}\cite{martinloef84} of descriptions. To give an
example; the following |Desc| datatype can describe the unit type,
pairs and products:

\begin{code}
data Desc : Set where
  `1 : Desc
  _⊕_ : Desc → Desc → Desc
  _⊗_ : Desc → Desc → Desc
\end{code}

These descriptions can be used to describe, for instance, booleans as
|`1 ⊕ `1|. Descriptions are decoded to types using the |⟦_⟧desc|
function:

\begin{code}
⟦_⟧desc : Desc → Set
⟦ `1 ⟧desc = ⊤
⟦ A ⊕ B ⟧desc = Either ⟦ A ⟧desc ⟦ B ⟧desc
⟦ A ⊗ B ⟧desc = ⟦ A ⟧desc × ⟦ B ⟧desc
\end{code}

When the decoding of a description |D| produces a type which is
isomorphic to a type |X|, we can say that |D| describes |X|. Indeed we
see that |⟦ `1 ⊕ `1 ⟧desc| normalises to |Either ⊤ ⊤|, a type which is
isomorphic to the type for booleans. Generic programming frameworks
like Haskell's generic deriving mechanism \cite{magalhaes10}
automatically derive an \emph{embedding-projection} pair
\cite{noort08} that converts between elements of the decoded
description and elements of the real datatype. An embedding-projection
pair for booleans can be defined as follows:

\begin{code}
bool-to : Bool → ⟦ `1 ⊕ `1 ⟧desc
bool-to false = left tt
bool-to true = right tt

bool-from : ⟦ `1 ⊕ `1 ⟧desc → Bool
bool-from (left tt) = false
bool-from (right tt) = true
\end{code}

%Ornaments
By choosing more advanced descriptions, more of Agda's datatypes can
be described. One may add support for recursion (with self-reference
as in naturals and lists), for datatype parameters, or for
indices. Descriptions can be used as a foundation to define
ornaments. An ornament is written as a patch for an existing
description, and can be applied to get a new description. In this way,
the ornament expresses the relation between the original description
and the ornamented description.

%Generating datatypes from descriptions
When ornaments are used to compute new descriptions, it would also be
convenient if new datatypes could be generated from computed
descriptions. Most generic programming frameworks do not require this
feature, because they never make modifications to descriptions. The
availability of this feature puts some unique constraints on the
definition of descriptions, because every description must be
convertible to a real datatype. We have to be careful that the sums
and products in our descriptions can never occur in the wrong
places---For instance, a description |(`1 ⊕ `1) ⊗ (`1 ⊕ `1)| can
describe a pair of booleans, but is not isomorphic to just one
datatype. At least two datatypes (the product type and |Bool| for
example) have to be used to get a type that is isomorphic to |⟦ (`1 ⊕
`1) ⊗ (`1 ⊕ `1) ⟧desc|.

Agda provides a \emph{reflection} mechanism which can be leveraged to
build the generic deriving and declaring framework. With reflection,
existing datatype declarations can be inspected and descriptions can
be generated for them. The functions constituting the
embedding-projection pair can be generated as well. The current
version of Agda (2.5.1) does not yet allow the declaration of new
datatypes, but we can do this semi-automatically by generating the
types for the individual constructors.

In this thesis we combine reflection, generics and ornaments to build
a library with which we can perform operations on user defined Agda
datatypes. The following contributions are made:

\begin{enumerate}
\item A universe of descriptions is built to encode datatypes. The
  descriptions support dependent types (\cref{chap:simple}) by passing
  along a context within the constructors. Multiple parameters and
  multiple indices can be encoded (\cref{chap:extended}) and the names
  of arguments can be stored (\cref{chap:named}). The descriptions are
  structured such that they are guaranteed to be convertable to Agda
  datatypes, so modifications to descriptions can be made freely
  without having to worry whether the resulting description makes
  sense or not.
\item Ornaments are defined for each version of these descriptions
  (section \ref{sec:sop-ornaments}, \ref{sec:simple-ornaments},
  \ref{sec:ext-ornaments} and \ref{sec:named-descriptions}). The
  ornaments allow insertion and deletion of arguments, refinement of
  parameters and refinement of indices. Many ornament-related concepts
  are translated to our universe, including ornamental algebras,
  algebraic ornaments (section \ref{sec:ext-algorn}) and reornaments
  (section \ref{sec:ext-reornaments}. Some high-level operations are
  defined which can be used to modify descriptions without having deep
  knowledge of our implementation (\cref{sec:named-moreornaments}).
\item We implement a framework which uses reflection to derive
  descriptions and their embedding-projection pairs for real datatypes
  (\cref{chap:named}). Some operations like fold and depth are defined
  generically, to work on every datatype for which a description has
  been derived (\cref{sec:named-generic}). Ornaments can be applied to
  descriptions, and these descriptions can be used to
  semi-automatically declare the corresponding datatype
  (\cref{sec:named-unquoting}).
\end{enumerate}

With these contributions we hope to provide a framework which can be
used for experimentation with ornaments, as well as a practical
example of how ornaments can be integrated into a language. Along the
way a library for the reflection of datatypes has been built which, to
our knowledge, does not yet exist for Agda.
