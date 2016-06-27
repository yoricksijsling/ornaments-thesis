%include thesis.fmt

\chapter{Conclusion}\label{chap:conclusion}

In this thesis we have presented a generic programming framework for
Agda. Datatypes can be transformed into new datatypes by a process of
quoting, ornamenting and unquoting.

A universe of descriptions has been implemented that can describe
inductive families. Dependent types are supported, so types of
arguments can depend on other arguments. Universes like these usually
allow a lot of types that could not be implemented with a single Agda
datatype. Our descriptions are uniquely capable of describing
inductive families and dependent types while still keeping to a
\emph{subset} of Agda datatypes.

Work on representing dependent types in type theory \cite{mcbride10}
is combined with work on generic programming with dependent types
\cite{chapman10}, resulting in descriptions that pass along contexts
internally. This idea restricts the use of arguments to exactly those
places where they could be used in an Agda datatype.
\Cref{sec:sop-Σdesc} and \cref{sec:discussion-ri} have shown that
these universes with contexts are still implementing inductive types
(for those in \cref{chap:simple}) or inductive families (in
\cref{chap:extended}). Parameters and indices are represented as
contexts as well, to effectively allow multiple parameters and
multiple indices that can depend on earlier parameters or indices
respectively.

Ornaments were adapted to our universe of descriptions as well. We
already knew that types where closed under ornamentation (because
every ornament results in a description). Our descriptions describe a
subset of Agda datatypes and each ornament results in a description.
This leads us to an interesting conclusion: With ornaments as we have
defined them, \emph{Agda datatypes are closed under
  ornamentation}. This means that ornamentation of \emph{actual}
datatypes can be implemented in a way that will not produce types that
can not be represented as a datatype.

The low-level ornaments were shown te be well-suited for
abstraction. We were able to implement higher-level ornaments for
concepts like 'renaming arguments' and 'adding a parameter'. This
shows that it is possible to provide an easier interface to
ornamentation that requires only a limited understanding of ornaments.

Datatypes can be quoted to descriptions, and descriptions can be
unquoted to datatypes. This allows users to obtain descriptions
without having to write them, and to use descriptions without having
to work without having to use representations of values like |⟨ 1 , x
, xs , refl ⟩|. Generic programming frameworks like Haskell's generic
deriving have already shown the strength of approaches like these.

\section{Future work}

Some limitations of the current implementation were already explained
throughout this thesis. We provide some directions for future research
based on these limitations. Some of these directions involve
fundamental changes to how the descriptions and their ornaments
work. Others are more practically oriented, to make the library easier
to use.

The separation of parameters from local contexts, explained in
\cref{sec:ext-separateparams}, is an obvious candidate for
implementation. We already know that the descriptions themselves can
be implemented in this way. This would make it possible to implement
reornaments on descriptions with parameters
(\cref{sec:ext-reornaments}) and the |addParameterArg| function of
\cref{sec:named-moreornaments} could add the parameter argument in
other places than at the front of a constructor.

Ornaments on inductive-recursive types are not well researched
yet. We do not know whether ornaments, quoting and unquoting work for
inductive-recursive types. If one wishes to support all types that can
be represented by Agda datatypes, this would certainly need to be
researched further.

Mutually recursive datatypes usually fall under the inductive
families, because inductive arguments can use indices to indicate
which of the types is being referred to. Our |ConDesc|/|DatDesc|
descriptions do not support mutually recursive types, but there does
not seem to be a fundamental reason why this would not be
possible. One could add another layer of descriptions to describe
bunches of |DatDesc|s and use indexed Σ-descriptions to inform the
semantics and ornaments of them. If one description can describe
multiple datatypes, it may even be possible to split one datatype into
multiple datatypes by refining the index that picks the datatype from
the bunch.

Our universe of descriptions does not allow many generic
operations. In \cref{sec:discussion-params} we show how parameter use
can be made explicit, so functions like |flatten| or |sum| could be
implemented generically. The same idea of making the meaning of
arguments more explicit can be expanded upon, to the point of
implementing a full language describing dependent types (a la McBride
\cite{mcbride10}). Quoting and unquoting of arguments to/from such a
representation is a whole new issue.

The unquoting of datatypes is not entirely automatic yet
(\cref{sec:named-unquoting}). We did solve all the problems regarding
the unquoting of the \emph{types of} the constructors and of the
datatype itself. It would be nice if Agda supported the unquoting of
datatypes within the |TC| monad. As an alternative solution, one might
implement functionality within the development environment that helps
with code generation. One can imagine how the user could instruct the
environment to write a datatype definition based on a description, and
that the user is then prompted to provide the name for each
constructor.

Some simple superficial improvements could be made to the descriptions
that are being quoted. They can be modified to allow hidden arguments,
such that a constructor like |cons| for |Vec| does not need to have
the length index as a visible argument. Contexts could be made to
support hidden arguments and names as well, then parameters and
indices can contain hidden arguments and the arguments are named
properly when the datatype is unquoted. Other more practically
oriented modifications could be made to the |HasDesc| record. The
structure with |Embeddable| and |Projectable| records as proposed in
\cref{sec:named-ep-instances} would probably be better suited for
generic programming.


\chapter*{Acknowledgements}

I would like to thank my supervisor Wouter Swierstra for getting me
interested in dependent types, for his helpful comments and for many
interesting discussions. His positive attitude and personal mentoring
never failed to cheer me up when i had a rough time. His engagement
during the whole process is truly appreciated. I also thank Johan
Jeuring for taking the time to read and assess this work.

Furthermore i want to thank the developers of Agda for the continued
development of a great dependently typed programming language, Andres
Löh for making writing easier with lhs2TeX, Pierre-Évariste Dagand for
a good discussion about ornaments, the software-technology reading
club for lots of interesting sessions, and my university buddies for
lots of \emph{fun}.

I am grateful to Maartje for her love and support, i could not have
done this without her. She is my motivation and inspiration to do the
best i can.
