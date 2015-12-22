%include proposal.fmt

\section{Introduction}\label{sec:introduction}

With the introduction of indexed datatypes (GADTs), functional
programmers are now able to capture invariants of their programs with
their data.
Encoding invariants in datatypes is yet another step towards writing
correct-by-construction software.
However, it can be a significant obstacle for code reuse.
Functions which work on one datatype do not work on a similar data
type with added invariants.
For example; vectors are the same as lists with an extra length index,
but the append (++) function for lists does not work for vectors.

Algebraic ornaments capture the relationship between two datatypes
with the same recursive structure.
Ornaments can be used to guide the transformation of functions which
work on the first datatype to functions which work on the
second\cite{dagand14-transporting, williams14}.
For instance to transform addition on natural numbers to append on lists.

This topic has been explored and formalized using category theory
\cite{dagand12, kogibbons13} and in Agda \cite{dagand14-transporting,
  dagand14-essence}.
The Agda implementations require you to describe your datatypes
within a universe of descriptions.
These descriptions can be interpreted as a datatype, but this approach
is not ideal for programming.

In this project we will work towards a more practical way to use
ornaments in Agda.
We want to be able to define datatypes as usual and define ornaments
on these datatypes.
Ornamenting a datatype should result in a newly defined datatype.
