%include thesis.fmt

\chapter{Discussion}\label{chap:discussion}

The structure of our descriptions match closely with the structure of actual datatype declarations. Only those parts which can contain arbitrary terms are represented as higher order arguments in our descriptions.

\section{Indexed containers}

What are containers? They are entirely higher-order, while our descriptions are mostly first-order. Containers are useful when one only cares about the behavior of the datatypes (semantic vs ..).

\section{How ornaments influence the choice of descriptions}

\section{Comparison with IODesc}

\section{Williams, Dagand, Remy: Ornaments in practice}

What's the overlap, what are the differences?

\section{Encoding argument types}

We doen dit nu met een functie (⟦ Γ ⟧ → Set). Dit is bedoelt om
arbitraire terms te kunnen representeren, die wel gebruik kunnen
maken van een context. Voor de implementatie van bepaalde generieke
functies zoals toList of toJson zou je willen herkennen wanneer de
term enkel een verwijzing naar een parameter is (`top`). Met deze
representatie is dat niet mogelijk. We zouden deze terms kunnen
reifyen, bijvoorbeeld met een beperkt datatype (CxTerm = topTerm ||
otherTerm (⟦ Γ ⟧ → Set)), of idealiter door de volledige taal te
internaliseren.
