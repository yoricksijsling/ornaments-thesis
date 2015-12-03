%include lhs2TeX.fmt
%include polycode.fmt

\section{Proposal overview}\label{sec:proposal-overview}

With increasing usage of GADTs, with logical invariants encoded in
their indices, programmers are often defining almost identical
functions for different data types.
Existing abstractions do not help us with this problem.
Ornaments are a novel abstraction mechanism to make code reuse between
similar data types possible.

Ornaments are actively researched \cite{mcbride11, dagand12,
  kogibbons13, dagand14-essence, dagand14-transporting, williams14}
and have great potential to make the lifes of depently typed
programmers better.
They provide insight into how data types relate to each other, which
seems fundamental for future work on functional programming languages.

In current implementations, users have to convert their data types to
a description universe manually, which is a very cumbersome process.
To stimulate actual usage and experimentation it is imperative to make
ornaments easier to use for the average Agda programmer.

One practical implementation has been done in Ornaments in Practice
\cite{williams14}, where the authors have made an effort to extend a
subset of ML with ornaments.
It is a great example of what ornaments could look like in a real
programming language.

\subsection{Research questions}

The main research question for this thesis is:

\begin{shaded}
Ornamentation has been shown to work on paper, can they be implemented
in a way which is user friendly?
\end{shaded}

A partial answer is already given by Ornaments in Practice
\cite{williams14}.
Our focus is a bit different in several ways:

\begin{itemize}
\item We use generic programming to define the ornaments directly in
  the host language.
  This enables users to directly work with the ornaments themselves.
\item We aim to be able to generate new data types using ornaments,
  which is not possible in the approach by Williams et al.
\end{itemize}

Our aims are:

\begin{enumerate}
\item Implement a library for generic programming in Agda.
  It must be able to take an existing data type and lift it to the
  generic representation.
\item Implement ornaments for the generic representations.
\item Use the gained knowledge to make reasonable guesses as to what
  we could do with ornaments in a practical setting.
\end{enumerate}

