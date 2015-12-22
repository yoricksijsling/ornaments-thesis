%include proposal.fmt

\section{Plan}\label{sec:plan}

In the first phase of the thesis project we have studied the
literature and have implemented a simple quoting library.
The next phase will be focused on working towards a library in which
we can apply ornaments to these quoted types.
We present a step-by-step plan, which we will definitely not be able
to complete.

\subsection{Unquoting new datatypes}\label{sec:plan-new-types}

In the current prototype we are able to quote a datatype to a
|SafeDatatype|.
We want to be able to unquote a new datatype from the
|SafeDatatype|, which would give us a new
|NamedSafeDatatype|.
This procedure can not be implemented as an Agda function, since it
has the side effect of introducing new names.
We can keep the number of manual steps small, and we hope that a
future version of Agda will allow us to properly unquote datatypes.
It is useful to do this step early, to figure out how unquoting of
datatypes works with a simple universe.

\subsection{Ornaments - Extensions}\label{sec:plan-extensions}

We can try to make simple modifications to datatypes by defining
functions on |SafeDatatype|.
One such operation which might be fun to experiment with is taking the
derivative (this makes a zipper).
The derivative is not essential for our goals, but it might provide insight.

When that works we define a type for extensions to datatypes, as
described in section \ref{sec:lit-extensions}.

\subsection{Indices}\label{sec:plan-indices}

The universe of the prototype does not support indices.
To solve this, we will implement the universe for indexed functors as
described in section \ref{sec:lit-indexed}.

The first step is to use this universe without adding new
functionality, so without changing |SafeDatatype|.
This will introduce some fundamental changes, so it might be quite a
challenge.
Once that works, we can extend the quoting and |SafeDatatype| to allow
indices.

\subsection{Ornaments - Refinements}\label{sec:plan-refinements}

When extensions and indices are implemented, we can continue with the
other half of ornaments: refinements (section \ref{sec:lit-refinements}).

At this point we should be able to implement some interesting examples
and we can experiment.

\subsection{Mutually recursive types}\label{sec:plan-mutual}

A single indexed description can describe a family of mutually
recursive datatypes, but the quoter and |SafeDatatype| do not yet
support it.
If |MultiSafeDatatype| is a variant of |SafeDatatype| which allows
mutually recursive types, we would be able to transform any indexed
description to a |MultiSafeDatatype| by first applying a normalisation
step.
This would free us from having to work with |SafeDatatype| for
functions which transform types.
In particular, ornaments could then work directly on the indexed
description instead of on |SafeDatatype|.

\subsection{Dependent types}\label{sec:plan-deptypes}

It would be nice if types of arguments could depend on arguments
before it.
The |Σ| constructor is required for this, to encode dependent pairs.
More real-world datatypes could then be supported by the library.

\subsection{Strictly positive types}\label{sec:plan-spt}

The prototype does not yet support functions as arguments.
We could add this functionality by adding a |Π| constructor for
(dependent) arrows in the indexed description type.
Support for this would enable us to quote all strictly positive types,
but we have to be careful that we do not allow variables in the wrong positions\cite{altenkirch06}.
