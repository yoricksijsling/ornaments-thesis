%include thesis.fmt

\chapter{Discussion}\label{chap:discussion}

The structure of our descriptions match closely with the structure of actual datatype declarations. Only those parts which can contain arbitrary terms are represented as higher order arguments in our descriptions.

\section{A language for arguments}

% In our descriptions, 'types within a context' are represented as a
% function |⟦ Γ ⟧ → Set|. With it, arbitrary types can be
% represented. The lack of a proper reification of these types does have
% its drawbacks, which we will be discussing in \todo{ref language for
%   terms}.

In essence, the problem of encoding dependent types is the same
problem as encoding terms in the language. Because terms can be types,
the entire syntax of terms has to be supported to properly encode all
possible types. There have been attempts to encode type theory within
type theory, or in other words, to \emph{internalise} the syntax and
semantics of type theory \cite{danielsson2007, mcbride10}. Building a
complete internalisation of terms is a lot of work and out of scope
for this thesis.

We doen dit nu met een functie (⟦ Γ ⟧ → Set). Dit is bedoelt om
arbitraire terms te kunnen representeren, die wel gebruik kunnen
maken van een context. Voor de implementatie van bepaalde generieke
functies zoals toList of toJson zou je willen herkennen wanneer de
term enkel een verwijzing naar een parameter is (`top`). Met deze
representatie is dat niet mogelijk. We zouden deze terms kunnen
reifyen, bijvoorbeeld met een beperkt datatype (ArgTerm = topTerm ||
otherTerm (⟦ Γ ⟧ → Set)), of idealiter door de volledige taal te
internaliseren.

De |rec-⊗_| is nu ook erg beperkt, omdat het alleen directe recursieve
calls toestaat. Dit datatype kan nu niet:

\begin{code}
data ListTree (A : Set) : Set where
  node : List (ListTree A) → ListTree A
\end{code}

Je zou dus eigenlijk |rec-⊗_| weg willen halen en in |ArgTerm|
opnemen. Dit is vermoedelijk ook de plek waar Π-types verwerkt kunnen
worden. Je moet in |CxTerm| ook iets doen om negatieve occurences van
rec te voorkomen.

Als je een systeem zoals 'outrageous but meaningful coincidences'
hebt, krijg je context-indexed terms. Om ook recursie en
strict-positivity te ondersteunen wil je, net als de semantiek van
descs, een context-indexed pattern functor opleveren.


\section{Indexed containers}

What are containers? They are entirely higher-order, while our descriptions are mostly first-order. Containers are useful when one only cares about the behavior of the datatypes (semantic vs ..).

\section{How ornaments influence the choice of descriptions}

\section{Comparison with IODesc}

\section{Williams, Dagand, Remy: Ornaments in practice}

What's the overlap, what are the differences?
