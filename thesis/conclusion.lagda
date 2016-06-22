%include thesis.fmt

\chapter{Conclusion}\label{chap:conclusion}

Show that we indeed contribute what we claimed.

How ornaments/unquoting influenced descriptions.

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

\subsection{Transporting functions over ornaments}


\chapter*{Acknowledgements}


I would like to thank my supervisor Wouter Swierstra for getting me
interested in dependent types, for his helpful comments and for many
interesting discussions. His positive attitude and personal mentoring
never failed to cheer me up when i had a rough time. His engagement
during the whole process is truly appreciated.

I am grateful to Maartje for her love and support, i could not have
done this without her. She is my motivation and inspiration to do the
best i can.
