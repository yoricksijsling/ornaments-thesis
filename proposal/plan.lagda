%include lhs2TeX.fmt
%include polycode.fmt

\section{Plan}\label{sec:plan}

In the first phase of the thesis project we have studied the
literature and have implemented a simple quoting library.
The next phase will be focused on working towards a library in which
we can apply ornaments to these quoted types.
In the next section we identify the milestones in this process, and
then we explain how we prioritize these milestones in section
\ref{sec:plan-priorities}.

\subsection{Milestones}

\subsubsection{Unquoting new data types}\label{sec:plan-new-types}

In the current prototype we are able to quote a data type to a
\texttt{SafeDatatype}.
We want to be able to unquote a new data type from the
\texttt{SafeDatatype}, which would give us a new
\texttt{NamedSafeDatatype}.
This procedure can not be implemented as an Agda function, since it
has the side effect of introducing new names.
We can keep the number of manual steps small, and we hope that a
future version of Agda will allow us to properly unquote data types.

\subsubsection{Ornaments - Extensions}\label{sec:plan-extensions}

We can try to make simple modifications to data types by defining
functions on \texttt{SafeDatatype}.
One such operation which might be fun to experiment with is taking the
derivative (this makes a zipper).
The derivative is not essential for our goals, but it might provide insight.

When that works we define a type for extensions to data types.
Extensions are half of what ornaments are; they can only attach data
to constructors.

\subsubsection{Indices}\label{sec:plan-indices}

The prototype does not support context free types with multiple fix
points.
One of the drawbacks, as explained in section \ref{sec:lit-cft-multi},
is that we can not handle data type indices.

We will have to formalise indexed descriptions (section
\todo{ref}), then we modify \texttt{SafeDatatype} and the quoter to
allow quoting of data types with indices.
This will introduce fundamental changes in many parts of the library,
so it might be quite a challenge.

\subsubsection{Ornaments - Refinements}\label{sec:plan-refinements}

When extensions and indices are implemented, we can continue with the
other half of ornaments: refinements. \todo{ref to refinements}

At this point we should be able to implement some interesting examples
and we can experiment.

\subsubsection{Strictly positive types}\label{sec:plan-spt}

The prototype only supports arguments which refer to the data type
itself or to a Set₀ data type parameter.
We would like to allow other kinds of terms in the arguments.
For instance, functions in arguments would enable us to quote all
strictly positive types.

\subsubsection{Mutually recursive types}\label{sec:plan-mutual}

Indexed descriptions allow mutually recursive data types, but
a \texttt{SafeDatatype} which works for indexed data types would not
automatically support mutually recursive types.
If \texttt{MultiSafeDatatype} would be a variant of
\texttt{SafeDatatype} which would allow mutually recursive types, we
would be able to transform any indexed description to a
\texttt{MultiSafeDatatype} by first applying a normalisation step.

This would free us from having to work with \texttt{SafeDatatype} for
functions which transform types.
In particular, ornaments could then work directly on the indexed
description instead of on \texttt{SafeDatatype}.

\subsubsection{Dependent types}\label{sec:plan-deptypes}

It would be nice if we could encode and quote dependently typed
constructors.
More real-world data types could then be supported by the library.

\subsubsection{Lifting functions over ornaments}\label{sec:plan-lifting}

If we could lift functions over ornaments, we would be able to utilise
the ornaments to actually write less code.
It would be a major step in making ornaments something you would
actually use.

\subsection{Priorities}\label{sec:plan-priorities}

The primary goal is to implement the first four milestones: unquoting
new data types, extensions, indices and refinements.
This is what we definitely want to reach in this project and they will
be executed in that order.

If it all goes well we will have time to continue with some other
extensions to the library.
We postpone the decision of which task we choose until that moment.
At that point we should be able to make a better estimation of what is
easy or hard, and how much time each task will take.
