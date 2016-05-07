%include thesis.fmt

% \section{Abstract}\label{sec:abstract}

% Todo.

\section{Introduction}\label{sec:introduction}

Something something

We present the following contributions:
\begin{itemize}
\item We built a universe of descriptions which can encode
  datatypes. It supports datatypes with parameters, indices and
  dependent types. Contrary to common approaches, our universe is
  conservative in the sense that only datatypes which can exist in the
  host language can be encoded in the universe. This allows us to
  perform mutations on descriptions freely, while still being certain
  that we can convert it back to an actual datatype. We explain how
  the universe is used in section \todo{ref}.
\item We have implemented a framework which uses metaprogramming to
  derive descriptions of real datatypes. The embedding-projection pair
  is also derived, allowing us to convert values of the original
  datatype to elements in our universe and back. Our implementation
  does not require the user to enable set-in-set or to disable
  strict-positivity checking, ensuring usability within existing
  systems. \todo{ref}.
\item We have implemented a way to extend and refine descriptions,
  based on the theory of ornaments. These are explained in section
  \todo{ref}.
\end{itemize}
