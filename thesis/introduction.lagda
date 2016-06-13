%include thesis.fmt

\chapter{Introduction}\label{chap:introduction}

Modern dependently typed languages like Agda support indices and
dependent types in their datatypes, allowing us to construct inductive
families \cite{dybjer91}. Types can contain extra information in their
indices, allowing us to place more precise restrictions on which
values are allowed in certain places. For instance, we might try to
define a function which takes a number of elements from the front of a
list.

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
return a default value, like |[]|, but such behavior may hide bugs
which would be discovered otherwise. Another solution is to change the
return type to |Maybe (List A)|, so |nothing| can be returned. This
lets the call site deal with error handling. An entirely different
approach is to avoid the situation by restricting the types
appropriately. When the list is at least of length |n|, the failure
can never occur. The type can be restricted by adding a length index
to the |List| type, resulting in the following |Vec| datatype:

\begin{code}
data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)
\end{code}

A new take function for |Vec| can be defined, which only accepts lists
of at least length |n|:

\begin{code}
takeᵥ : ∀{A m} → (n : Nat) → Vec A (n + m) → Vec A n
takeᵥ zero _ = []
takeᵥ (suc n) (x ∷ xs) = x ∷ takeᵥ n xs
\end{code}

By adding the proper indices, logic of the program can be encoded
within a datatype. Building datatypes such that they precisely match
the logic of the program is an essential aspect of writing
correct-by-construction programs in functional programming
languages. This specialization of datatypes can however be a obstacle
to code reuse. For example; one may have defined a function to find
the smallest value in a list of natural numbers:

\begin{code}
smallest : List Nat → Maybe Nat
smallest [] = nothing
smallest (x ∷ xs) with smallest xs
smallest (x ∷ _) | nothing = just x
smallest (x ∷ _) | just m = just (if (lessNat x m) then x else m)
\end{code}

Although we explain |Vec|s as being a |List| with a length index, it is
\emph{defined} as an entirely separate thing. Agda has no idea that
these two are related. To get the lowest value in a |Vec| of naturals,
we have to define an entirely new function:

\begin{code}
smallestᵥ : ∀{n} → Vec Nat n → Maybe Nat
smallestᵥ [] = nothing
smallestᵥ (x ∷ xs) with smallestᵥ xs
smallestᵥ (x ∷ _) | nothing = just x
smallestᵥ (x ∷ _) | just m = just (if (lessNat x m) then x else m)
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
datatype which can all be used under different circumstances.

It may prove useful if Agda knew about the connections between all
these different variants of datatypes. Conor McBride \cite{mcbride11}
has presented \emph{ornaments} as a way to express relations between
datatypes. Loosely speaking, one type can be said to be an ornament of
another if it contains more information in some way, for example by
the refinement with indices or the addition of data. They can be used
to express that |Vec| is an ornament of |List|. Or that |List| can be
defined as an ornament on |Nat|, by attaching an element of type |A|
to each |suc| constructor. To start working with ornaments we need to
model datatypes within Agda itself.

Datatype-generic programming uses \emph{descriptions} to describe
types. In Agda these descriptions often take the form of a datatype,
which is combined with a function which assigns a type to every
description \cite{altenkirch06}. For example; the following |Desc|
datatype can describe the unit type, pairs and products:

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
isomorphic to the type for booleans. An \emph{embedding-projection}
pair \cite{noort08} converts between elements of the decoded
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

%Deriving descriptions from datatypes
Datatype-generic programming, and by extension the use of ornaments,
is not practical unless there is an easy way to connect actual
datatypes with descriptions. The generic deriving \cite{magalhaes10}
mechanism in Haskell automatically derives the description and
embedding-projection pair for a user-defined datatype.

%Generating datatypes from descriptions
When ornaments are used to build new descriptions, it would also be
convenient if new datatypes could be generated from computed
descriptions. Most generic programming frameworks do not require this
feature, because they never make modifications to descriptions. The
availability of this feature puts some unique constraints on the
definition of descriptions, because every description must be
convertible to a real datatype. We have to be careful that the sums
and products in our descriptions can never occur in the wrong
places---For instance, a description |(`1 ⊕ `1) ⊗ (`1 ⊕ `1)| can
describes a pair of booleans, but that is not representable in a
single datatype. Two datatypes (for instance |Either| and |Bool|) have
to be used to get a type isomorphic to |⟦ (`1 ⊕ `1) ⊗ (`1 ⊕ `1)
⟧desc|.

Agda provides a \emph{reflection} mechanism which can be leveraged to
build the generic deriving and declaring framework. With reflection,
existing datatype declarations can be inspected and new descriptions
can be generated. The functions constituting the embedding-projection
pair can be generated as well. The current version of Agda (2.5.1)
does not yet allow the declaration of new datatypes, but we can do
this semi-automatically by generating the types for the individual
constructors.

In this thesis we combine reflection, generics and ornaments to build
a library with which we can perform operations on user defined Agda
datatypes. The following contributions are made:

\begin{enumerate}
\item A universe of descriptions is built to encode datatypes. The
  descriptions support dependent types (\fref{chap:simple}) by passing
  along an environment within the constructors. Multiple parameters
  and multiple indices can be encoded (\fref{chap:extended}) and the
  names of arguments can be stored (\fref{chap:named}). The
  descriptions are structured such that they are guaranteed to be
  convertable to Agda datatypes, so modifications to descriptions can
  be made freely without having to worry whether the resulting
  description makes sense or not.
\item Ornaments are defined for each version of these descriptions
  (section \ref{sec:sop-ornaments}, \ref{sec:simple-ornaments},
  \ref{sec:ext-ornaments} and \ref{sec:named-ornaments}). The
  ornaments allow refinement using indices and insertion and deletion
  of arguments. Many ornament-related concepts are translated to our
  universe, including ornamental algebras, algebraic ornaments
  (section \ref{sec:ext-algorn}) and reornaments (section
  \ref{sec:ext-reornaments}. Some high-level operations are defined
  which can be used to modify descriptions without knowing anything
  about the implementation of ornaments \todo{ref}.
\item We implement a framework which uses reflection to derive
  descriptions and their embedding-projection pairs for real datatypes
  (\fref{chap:named}). Some operations like fold and depth are defined
  generically, to work on every datatype for which a description has
  been derived \todo{ref}. Ornaments can be applied to descriptions,
  and these descriptions can be used to semi-automatically declare the
  corresponding datatype.
\end{enumerate}

With these contributions we hope to provide a framework which can be
used for experimentation with ornaments, as well as a practical
example of how ornaments can be integrated into a language. Along the
way a library for the reflection of datatypes has been built, which
does not yet exist for Agda as far as we are aware.
