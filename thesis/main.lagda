\documentclass[a4paper]{article}

\usepackage[english]{babel}
\usepackage{graphicx}
\usepackage{hyperref}
\usepackage{prettyref}
\usepackage[draft]{todonotes}
% \usepackage[disable]{todonotes}
% \usepackage{multirow}
\usepackage{alltt}
\usepackage{amsthm}
% \usepackage{parskip}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

% Frame color
\usepackage{framed,color}
\definecolor{shadecolor}{rgb}{1.0,0.9,0.7}

% Floats
\usepackage{float}
\newfloat{listing}{htbp}{ltg}
\floatname{listing}{Listing}

% Theorem styles
\newtheorem{theorem}{Theorem}[section]
\newtheorem{remark}{Remark}[section]
\newtheorem{conjecture}{Conjecture}[section]
\theoremstyle{definition}
% \newtheorem{example}{Example}[section]
\newtheorem{examplex}{Example}[section]
\newenvironment{example}
  {\pushQED{\qed}\renewcommand{\qedsymbol}{$\triangle$}\examplex}
  {\popQED\endexamplex}
\newtheorem{definition}{Definition}[section]

% Shortcuts
\newcommand{\definedin}[1]{\footnote{Module: #1}}

% Styling things
\newcommand{\args}[1]{\overline{#1}}
\newcommand{\ttargs}[1]{\(\args{\texttt{#1}}\)}
\newcommand{\ttunderline}[1]{\(\underline{\texttt{#1}}\)}
\definecolor{ttemph1}{HTML}{BB0000}
\definecolor{ttemph2}{HTML}{0000BB}
\newcommand{\codeemph}[2]{%
\ifnum#1=1\textcolor{ttemph1}{\textsf{\textbf{#2}}}%
\else\ifnum#1=2\textcolor{ttemph2}{\textsf{\textbf{#2}}}%
\else\textbf{#2}%
\fi\fi}

\newcommand{\Bool}{\textrm{Bool}}
\newcommand{\List}{\textrm{List}}
\newcommand{\Nat}{\textrm{Nat}} % or \mathit{N\!at}
\newcommand{\NatList}{\textrm{NatList}}
\newcommand{\PairOfBools}{\textrm{PairOfBools}}
\newcommand{\RoseTree}{\textrm{RoseTree}}
\newcommand{\Tree}{\textrm{Tree}}

%--------------------------------------------------

%  Agda mess

\usepackage[bw]{agda}
% \usepackage{agda}
\usepackage{catchfilebetweentags}
\newcommand{\AK}{\AgdaKeyword}
\newcommand{\AS}{\AgdaString}
\newcommand{\AY}{\AgdaSymbol}
\newcommand{\AN}{\AgdaNumber}
\newcommand{\AB}{\AgdaBound}
\newcommand{\AO}{\AgdaOperator}
\newcommand{\AI}{\AgdaInductiveConstructor}
\newcommand{\AC}{\AgdaCoinductiveConstructor}
\newcommand{\AD}{\AgdaDatatype}
\newcommand{\AF}{\AgdaFunction}
\newcommand{\AM}{\AgdaModule}
\newcommand{\AL}{\AgdaField}
\newcommand{\AR}{\AgdaArgument}
\newcommand{\AT}{\AgdaIndent}
\newcommand{\ARR}{\AgdaRecord}
\newcommand{\AP}{\AgdaPostulate}

% \newcommand{\InsertCodeInline}[2][Thesis.tex]{\codeinlinetrue\ExecuteMetaData[../src-tex/#1]{#2}}
% \newcommand{\InsertCode}[2][Thesis.tex]{
%   \codeinlinefalse
%   \medskip
%   \ExecuteMetaData[../src-tex/#1]{#2}

%   \medskip}
% \newcommand{\InsertCodeN}[2][Thesis.tex]{
%   \codeinlinefalse
%   \medskip
%   \ExecuteMetaData[../src-tex/#1]{#2}\refstepcounter{codeblock}\begin{center}Listing \thecodeblock\end{center}\label{code:#2}%

%   \medskip}

% \newcounter{codeblock}
% \newcommand{\labelcodeblock}[2]{\refstepcounter{codeblock}\label{#1}\begin{center}Listing \thecodeblock\end{center}}

%---

\newcommand{\greyFG}[1]{\textcolor[rgb]{0.15,0.15,0.15}{#1}}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\D}[1]{\blueFG{\textsf{##1}}} % Types
  % \newcommand{\V}[1]{\blackFG{\textsf{#1}}} % Variables
  \newcommand{\V}[1]{\greyFG{\textsf{##1}}} % Variables
  % \newcommand{\K}[1]{\mathbf{#1}}
  % \newcommand{\K}[1]{\orange{\textsf{\textbf{#1}}}} % Keywords
  \newcommand{\K}[1]{\orangeFG{\textsf{##1}}} % Keywords
}
\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}
\ColourStuff

%--------------------------------------------------

\setmainfont[ItalicFont = xits-italic.otf
, BoldFont = xits-bold.otf
, BoldItalicFont = xits-bolditalic.otf]{xits-regular.otf}
\setmathfont[BoldFont = xits-mathbold.otf]{xits-math.otf}
\setsansfont[Scale=MatchLowercase
, ItalicFont = DejaVuSans-Oblique.ttf
, BoldFont = DejaVuSans-Bold.ttf
, BoldItalicFont = DejaVuSans-BoldOblique.ttf]{DejaVuSans.ttf}
\setmonofont[Scale=MatchLowercase
, ItalicFont = DejaVuSansMono-Oblique.ttf
, BoldFont = DejaVuSansMono-Bold.ttf
, BoldItalicFont = DejaVuSansMono-BoldOblique.ttf]{DejaVuSansMono.ttf}

\newfontfamily{\xitsfont}[Scale=MatchLowercase]{xits-regular.otf}

\DeclareTextFontCommand{\textxits}{\xitsfont}

\usepackage{newunicodechar}

% \newunicodechar{●}{\textxits{•}}
% \newunicodechar{⌷}{\textxits{$\vrectangle$}}
% \newunicodechar{▱}{\textxits{\rotatebox[origin=c]{105}{▱}}}
\newunicodechar{⊎}{\textxits{⊎}}

%--------------------------------------------------

\title{Implementing Ornaments}
\date{\today}
\author{Yorick Sijsling}

\begin{document}

\maketitle

\begin{flushright}
\emph{Supervised by} Wouter Swierstra\\
\emph{Second examiner} Johan Jeuring
\end{flushright}

% \listoftodos
\input{introduction.tex}
\input{usage.tex}
\input{descriptions.tex}
\input{ornaments.tex}
\input{implementation.tex}
\input{discussion.tex}
\input{conclusion.tex}

\bibliographystyle{plain}
% \bibliographystyle{alpha}
% \bibliographystyle{apa}
\bibliography{main}

\end{document}
