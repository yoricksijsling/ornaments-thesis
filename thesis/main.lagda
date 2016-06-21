% \documentclass[a4paper]{report} % don't forget to disable the marker
\documentclass[draft,a4paper]{report}

\newif\ifsetmono
\setmonofalse

%include thesis.fmt

\usepackage{main}

%--------------------------------------------------

\title{Implementing Ornaments}
\date{\today}
\author{Yorick Sijsling}

\begin{document}

% \maketitle

% \begin{flushright}
% \emph{Supervised by} Wouter Swierstra\\
% \emph{Second examiner} Johan Jeuring
% \end{flushright}

\ifdraft{\listoftodos}{}
\input{abstract.tex}
\tableofcontents
% \input{presentationstuff.tex}
\input{introduction.tex}
\input{usage.tex}
\input{sop.tex}
\input{simple.tex}
\input{extended.tex}
\input{named.tex}
%%% \input{implementation.tex}
\input{discussion.tex}
\input{conclusion.tex}

\bibliographystyle{plain}
% \bibliographystyle{alpha}
% \bibliographystyle{apa}
\bibliography{main}

\end{document}
