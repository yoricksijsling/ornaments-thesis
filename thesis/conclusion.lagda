%include thesis.fmt

\chapter{Conclusion}\label{sec:conclusion}

Show that we indeed contribute what we claimed.

\section{Future work}

\subsection{Making indices dependent on parameters}

\subsection{Names in contexts}

\subsection{Real unquoting of datatypes}

\subsection{Interactive macros}

Calling macros from emacs. Automating prompting of inputs for those macros.

\begin{code}
data Prompt (A : Set) (s : String) : Set
  ret : (a : A) → Prompt A s
\end{code}

\subsection{Transporting funtions over ornaments}
