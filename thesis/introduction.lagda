%include thesis.fmt

\section{Introduction}\label{sec:introduction}

Modern dependently typed functional programming languages like Agda
and Idris support datatypes with dependent types and indexes. These
allow programmers to encode invariants of their programs within their
datatypes. Building your datatypes such that they precisely match
the logic of the program is an essential aspect of writing
correct-by-construction software in these languages.

This specialization of datatypes can however be a significant obstacle
to code reuse. Programmers frequently define practically the same
functions for slightly different datatypes. For example; vectors are
the same as lists with an extra length index, but the append (++)
function for lists does not work for vectors. Having to write this
function for both types violates the 'don't repeat yourself' software
development principle.

To start solving this problem, we have to capture the relationships
between different-but-similar datatypes. Ornaments have been invented
to do this; they formalise the notions of extension en refinements of
datatypes \todo{cite mcbride}. They can be generated in various ways
and can be used to build new datatypes. An ornament can guide the
implementation of functions which work on the work on the ornamented
datatype based on the implementation of that function on the
non-ornamented datatype \cite{dagand14-transporting, williams14}.

This topic has been explored and formalized using category theory
\cite{dagand12, kogibbons13} and in Agda \cite{dagand14-transporting,
  dagand14-essence}.  The Agda implementations require you to describe
your datatypes within a universe of descriptions, so to use it the
user is always working with generic representations of datatypes, not
with the datatypes themselves. This hinders usability and easy
experimentation.

A technology like ornaments has to be experimented with to reach its
potential. To facilitate this, we have implemented a more practical
way to use ornaments in Agda based on metaprogramming. With this
implementation, we can use actual Agda datatypes and define ornaments
for them. Along the way we have implemented a mechanism to derive
generic descriptions of datatypes supporting indices, parameters and
dependent types.
