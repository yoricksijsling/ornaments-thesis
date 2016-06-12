%include thesis.fmt

\chapter{Introduction}\label{chap:introduction}

Modern dependently typed languages like Agda support indices and
dependent types in their datatypes, allowing us to construct inductive
families \cite{dybjer91}. Types can contain extra information in their
indices, allowing us to place more precise restrictions on which
values are allowed in certain places. For instance, when functions
require lists which are of a certain length we might add a length
index to those lists to formalise that requirement. By adding the
proper indices, logic of the program can be encoded within a datatype.

Building datatypes such that they precisely match the logic of the
program is an essential aspect of writing correct-by-construction
programs in functional programming languages. This specialization of
datatypes can however be a significant obstacle to code reuse. For
example; one may have defined the |List| datatype and a function to
find the lowest value in a list of naturals:

\begin{code}
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

lowest : List Nat → Maybe Nat
lowest [] = nothing
lowest (x ∷ xs) with lowest xs
lowest (x ∷ _) | nothing = just x
lowest (x ∷ _) | just m = just (if (lessNat x m) then x else m)
\end{code}

The |Vec| datatype is very similar; it only adds a length index:

\begin{code}
data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)
\end{code}

Although we explain |Vec|s as being a |List| with an index, we
\emph{define} it as an entirely separate thing. Agda has no idea that
these two are related. To get the lowest value in a |Vec| of naturals,
the whole function has to be redefined:

\begin{code}
lowestᵥ : ∀{n} → Vec Nat n → Maybe Nat
lowestᵥ [] = nothing
lowestᵥ (x ∷ xs) with lowestᵥ xs
lowestᵥ (x ∷ _) | nothing = just x
lowestᵥ (x ∷ _) | just m = just (if (lessNat x m) then x else m)
\end{code}

Another example is found in the modeling of the simply-typed lambda
calculus. The datatype which describes the terms can be indexed by
their types, allowing the static enforcement of typing rules. For this
same datatype, it might also be useful to add the evaluation result as
an index to simplify reasoning about the preservation of behavior
during the mutation of terms \cite{mcbride11,
  dagand14-transporting}. The typing semantics and the evaluation
semantics both induce useful indices for the datatype. With and
without both of these indices, we can define four variants of the
datatype which can all be used under different circumstances.

It may prove useful if Agda knew about the connections between all
these different variants of datatypes. Conor McBride \cite{mcbride11}
has presented \emph{ornaments} as a way to express relations between
them. Loosely speaking, one type can be said to be an ornament of
another if it contains more information in some way, for example by
the refinement with indices or the addition of data. They can be used
to express that |Vec| is an ornament of |List|. |List| can in turn be
defined as an ornaments on |Nat|, by attaching an element of type |A|
to each |suc| constructor. To start working with ornaments we need to
model datatypes within Agda itself.

Datatype-generic programming is how we talk about datatypes within the
host language. In type theory this is done with a \emph{universe}
\cite{martinloef84}, which consists of two things: \emph{Descriptions}
or codes are used to describe types and a \emph{decoding function} provides a
semantics for these descriptions which gives the type they are meant to describe. By
choosing the right descriptions we hope to encode a sufficiently useful
subset of Agda's datatypes. Ornaments can then be defined to express
the relations between these descriptions.

Datatype-generic programming, and by extension the use of ornaments,
is not practical unless there is some way to connect the model with
the real thing. In the style of the generic deriving
\cite{magalhaes10} mechanism is Haskell, we want to be able to derive
a description for a datatype. Additionally, an
\emph{embedding-projection} pair \cite{noort08} is required to convert
between elements of the real datatype and elements of the
universe.

When ornaments are used to build new descriptions, a new feature for
the generic programming framework becomes convenient: The declaration
of datatypes by using a description. Most generic programming
frameworks do not require this feature, because they never make
modifications to descriptions. The availability of this feature puts
some unique constraints on the definition of descriptions, because
every description must be convertible to a real datatype. We have to
be careful that the sums and products in our descriptions can never
occur in the wrong places.

Agda provides a \emph{reflection} mechanism which can be
leveraged to build the generic deriving and declaring framework. With
reflection, existing datatype declarations can be inspected and
descriptions can be generated. The functions for the
embedding-projection pair can be generated as well. The current
version of Agda (2.5.1) does not yet allow the declaration of new
datatypes, but we can do this semi-automatically by generating the
types for the constructors.

In this thesis we combine reflection, generics and ornaments to build
a library with which we can perform operations on real Agda
datatypes. The following contributions are made:

\begin{enumerate}
\item A universe of descriptions is built to encode datatypes. The
  descriptions support dependent types (\fref{chap:simple}) by passing
  along an environment within the constructors. Multiple parameters
  and multiple indices can be encoded (\fref{chap:extended}) and the
  names of arguments can be stored (\fref{chap:named}). The
  descriptions are structured such  that they can be converted to real
  datatypes, so modifications to descriptions can be made freely
  without having to consider whether the resulting description makes
  sense or not.
  % The descriptions do not require the disabling of safety features
  % like strict-positivity, type-in-type or termination checking.
\item Ornaments are defined for these descriptions. The ornaments
  allow refinement using indices and insertion and deletion of
  arguments. Many ornament-related concepts are translated to our
  universe, including ornamental algebras, algebraic ornaments and
  reornaments. Some high-level operations are defined which
  can be used to modify descriptions without knowing anything about
  the implementation of ornaments.
\item We implement a framework which uses reflection to derive
  descriptions and their embedding-projection pairs for real
  datatypes. Some operations like fold and depth are defined
  generically, to work on every datatype for which a description has
  been derived. Ornaments can be applied to descriptions, and these
  descriptions can be used to semi-automatically declare the
  corresponding datatype. A generic function is given to apply an
  ornamental algebra, provided that both the original and the
  ornamented datatype have a derived description and that the ornament
  matches these descriptions.
\end{enumerate}

With these contributions we hope to provide a framework which can be
used for experimentation with ornaments, as well as a practical
example of how ornaments can be integrated into a language. Along the
way a generic deriving mechanism has been build, which does not yet
exist for Agda as far as we are aware.
