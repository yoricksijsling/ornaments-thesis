% \documentclass[a4paper]{report} % don't forget to disable the marker
\documentclass[draft,a4paper]{report}

\newif\ifsetmono
\setmonofalse

%include thesis.fmt

\usepackage{main}

%--------------------------------------------------

\title{Generic programming with ornaments and dependent types}
\date{\today}
\author{Yorick Sijsling}

\begin{document}

% \input{presentationstuff.tex}

\begin{titlepage}
\fontspec[ItalicFont = lmroman10-italic.otf
, BoldFont = lmroman10-bold.otf
, SmallCapsFont = lmromancaps10-regular.otf]{lmroman10-regular.otf}
\center
\textsc{\LARGE Utrecht University}\\[0.4cm]
\textsc{\Large Master Thesis Computing Science}\\[4.0cm]
{\Huge Generic programming with ornaments and dependent types}\\[1.5cm]
\large
% {\bfseries Yorick Sijsling}\\[4.0cm]
{\bfseries Yorick Sijsling}\\[4.0cm]
{\bfseries Supervisors}\\[0.1cm]
dr. Wouter Swierstra\\
prof. dr. Johan Jeuring\\
\vfill
\today
\end{titlepage}

\ifdraft{\listoftodos}{}
\input{abstract.tex}
\tableofcontents
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
\bibliography{main}

\end{document}
