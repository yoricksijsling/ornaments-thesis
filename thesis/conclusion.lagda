%include thesis.fmt

\section{Conclusion}\label{sec:conclusion}

Show that we indeed contribute what we claimed.

\subsection{Future work}

\subsubsection{Making indices dependent on parameters}

\subsubsection{Names in contexts}

\subsubsection{Real unquoting of datatypes}

\subsubsection{Interactive macros}

Calling macros from emacs. Automating prompting of inputs for those macros.

\begin{code}
data Prompt (A : Set) (s : String) : Set
  ret : (a : A) → Prompt A s
\end{code}

\subsubsection{Transporting funtions over ornaments}
