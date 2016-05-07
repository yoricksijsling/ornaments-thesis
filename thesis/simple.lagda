%include thesis.fmt

\section{Basic descriptions and ornaments}\label{sec:simple}

In this section we give a quick introduction to generics in functional
programming with the \emph{sum-of-products} approach.

In type theory this is implemented as a universe construction; meaning that we can build
codes and we have a decoding function which gives us a type
corresponding to a code. In this thesis we will be referring to codes
as \emph{descriptions}

extension to the usual sum-of-products descriptions which support
dependent types. We refer to these descriptions as 'simple'. We define
ornaments on these descriptions.

Terminology

\subsection{Background: Sum-of-products}

Generics using sum-of-products and fixpoints.

\subsection{Contexts}

Sum-of-products of previous section do not support dependent types. Show how contexts work and give a simplified definition of them.

\subsection{Introducing descriptions and their ornaments}

These descriptions are just sum-of-products with contexts. In this
subsection we show what the descriptions and ornaments look like.

\subsection{Descriptions}

The definition of |DatDesc| and |ConDesc|.

\subsection{Algebra and fold}

|DatAlg|, |fold|

\subsection{Ornaments}

Definition of |DatOrn| and |ConOrn|

\subsection{Ornamental algebras}

Definition of forget

\subsection{Discussion}

\begin{itemize}
\item Why is the Dat/Con split useful
\item Compare with Σdescs: With a Σ constructor, the description of
  the tail is given as a result of a function. Stuff like
  |countArguments| is not possible.
\item Choice of ornaments: Every ornament must give rise to an
  ornamental algebra. Ornaments can be interpreted as refinements
  (?). All of our ornaments can be derived from those in 'transporting
  functions', even though they use Σdescs. We do not have a
  'reconstructor' ornament which does insert/give on the top-level.
\end{itemize}
